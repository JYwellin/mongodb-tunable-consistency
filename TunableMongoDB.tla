------------------------------ MODULE TunableMongoDB ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* constants and variables
CONSTANTS Client, Server,  \* set of model value
          Key, Value,  \* set of model value
          Nil,  \* model value, place holder
          OpTimes,  \* op count at most
          PtStop, PtEpsilon  \* max physical time and max pt divergence

VARIABLES Primary, Secondary,  \* will be assigned when init
          Oplog, Store,  \* op log and kv store
          Ct, Ot,  \* some timestamps
          InMsgc, InMsgs,  \* client inbuf msg, server inbuf msg
          ServerMsg,  \* server heartbeat msgs
          BlockedClient,  \* Client operations in progress
          OpCount,  \* op count for each client
          Pt,  \* physical time for each server
          Cp,  \* commit point
          State,  \* state info of other servers
          SnapshotTable,  \* snapshotTable[s] : snapshot data set at server s
          Optimes  \* sorted state info of other servers

ASSUME Cardinality(Client) >= 1  \* at least one clinet
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1  \* at least one object
ASSUME Cardinality(Value) >= 2  \* at least two values to update

\* helpers
HLCLt(x, y) == IF x.p < y.p
               THEN TRUE
               ELSE IF x.p = y.p
                    THEN IF x.l < y.l
                         THEN TRUE
                         ELSE FALSE
                    ELSE FALSE
HLCMin(x, y) == IF HLCLt(x, y) THEN x ELSE y
HLCMax(x, y) == IF HLCLt(x, y) THEN y ELSE x
HLCType == [ p : Nat, l : Nat ]
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

PUT == "put"
GET == "get"

node_vars == <<Primary, Secondary>>
data_vars == <<Oplog, Store>>
time_vars == <<Ct, Ot>>
mesg_vars == <<InMsgc, InMsgs, ServerMsg>>
vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, ServerMsg, BlockedClient, OpCount, Pt, Cp, State, SnapshotTable >>

\* init
InitPrimary == Primary = CHOOSE s \in Server: TRUE
InitSecondary == Secondary = Server \ {Primary}
InitOplog == Oplog = [ s \in Server |-> <<>> ]
InitStore == Store = [ n \in Server \cup Client  |-> [ k \in Key |-> Nil ] ]
InitCt == Ct = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitOt == Ot = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitInMsgc == InMsgc = [ c \in Client |-> <<>> ]
InitInMsgs == InMsgs = [ s \in Server |-> <<>> ]
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitBlockedClient == BlockedClient = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitHbState == State = [ s \in Server |-> [ s0 \in Server \ {s} |-> 
                                              [ p |-> 0, l |-> 0 ] ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ n \in Server \cup Client  |-> [ k \in Key |-> Nil ] ],
                                                   commitstate |-> 0]>> ]                                        

Init == 
    /\ InitPrimary 
    /\ InitSecondary
    /\ InitOplog 
    /\ InitStore
    /\ InitCt 
    /\ InitOt 
    /\ InitPt 
    /\ InitCp
    /\ InitInMsgc 
    /\ InitInMsgs 
    /\ InitServerMsg
    /\ InitBlockedClient 
    /\ InitOpCount
    /\ InitHbState
    /\ InitSnap

\* snapshot
Snapshot == 
    /\ \E s \in Server:
       /\ SnapshotTable' = [SnapshotTable EXCEPT ![s] = Append(@, [ ot |-> Ot[s], store |-> Store[s], commitstate |-> 0]) ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, ServerMsg, BlockedClient, OpCount, Pt, Cp, State >>

\* TODO : which time to delete snapshot
RECURSIVE UpdateSnapshot_rec(_, _, _)
UpdateSnapshot_rec(cp, s, snapshot) ==
    IF ~ HLCLt(cp, snapshot[1].ot)  THEN UpdateSnapshot_rec(cp, s, Tail(snapshot))
                                    ELSE snapshot    
                                 
UpdateSnapshot(cp, s) == 
     SnapshotTable' =  [ SnapshotTable EXCEPT ![s] = UpdateSnapshot_rec(cp, s, SnapshotTable[s]) ]     
     
\* heartbeat

BroadcastHeartbeat(s) == 
    /\ LET msg == [ aot |-> Ot[s], s |-> s ]
       IN ServerMsg' = [ s0 \in Server \ {s} |-> Append(ServerMsg[s0], msg) ] @@
                       [ s |-> ServerMsg[s] ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs,
                   BlockedClient, OpCount, Pt, Cp, State>>

ServerTakeHeartbeat ==
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0
        /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]
        /\ Cp' = IF HLCLt(Cp[s], ServerMsg[s][1].cp) /\ 
                    ~ HLCLt(Ot[s], ServerMsg[s][1].aot)
                 THEN [ Cp EXCEPT ![s] = ServerMsg[s][1].cp]
                 ELSE Cp
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![ServerMsg[s][1].s] = 
                        ServerMsg[s][1].aot ]
            IN [ State EXCEPT ![s] = hb]
        /\  UpdateSnapshot(Cp'[s], s)   
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs,
                   BlockedClient, OpCount, Pt>>

\* commit point
sort(state) == state

AdvanceCp == 
    /\ \E s \in Server:
        /\ Optimes' = [ Optimes EXCEPT ![s] = sort(State[s]) ]
        /\ Cp' = Optimes'[s][Cardinality(Server) \div 2 + 1]
    
\* clock

UnchangedExPt == <<Primary, Secondary, InMsgc, InMsgs, ServerMsg, Oplog, Store,
                   Ct, Ot, BlockedClient, OpCount>>
UnchangedExCt == <<Primary, Secondary, InMsgc, InMsgs, ServerMsg, Oplog, Store,
                   Pt, Ot, BlockedClient, OpCount>>

MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] IN Pt[x]

NTPSync == /\ Pt' = [ s \in Server |-> MaxPt ]
           /\ UNCHANGED UnchangedExPt

AdvancePt == 
    /\ \E s \in Server: Pt[s] <= PtStop /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] /\
                        BroadcastHeartbeat(s)
    /\ UNCHANGED UnchangedExPt

Tick(s) == /\ Ct' = IF Ct[s].p >= Pt[s]
                    THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                     ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]
           /\ UNCHANGED UnchangedExCt

\* server

ReplicateOplog(s) == LET len_s == Len(Oplog[s])
                         len_p == Len(Oplog[Primary])
                     IN IF s /= Primary /\ len_s < len_p
                        THEN SubSeq(Oplog[Primary], len_s + 1, len_p)
                        ELSE <<>>

Replicate ==
    /\ \E s \in Secondary:
        /\ ReplicateOplog(s) /= <<>>
        /\ Oplog' = [ Oplog EXCEPT ![s] = Append(@, ReplicateOplog(s)) ]
        \* TODO: apply ReplicateOplog(s) one by one instead of copy Primary
        /\ Store' = [ Store EXCEPT ![s] = Store[Primary] ]
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], Ct[Primary]) ]  \* TODO
        /\ Ot' = [ Ct EXCEPT ![s] = HLCMax(Ot[s], Ot[Primary]) ]  \* TODO
        /\ UpdateSnapshot(Cp'[s], s) 
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot'[s] ]
            IN [ State EXCEPT ![s] = hb]
     /\ UNCHANGED <<Primary, Secondary, InMsgc, InMsgs, BlockedClient, OpCount,
                    ServerMsg, Pt>>

ServerGetReply_local ==
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = GET
        /\ InMsgs[s][1].rc = "local"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ Ot[s] >= InMsgs[s][1].ot
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] = 
            Append(@, [ op |-> GET, k |-> InMsgs[s][1].k, v |->
                        Store[s][InMsgs[s][1].k], ct |-> Ct'[s], ot |-> Ot[s]])]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ Pt[s] + PtEpsilon <= MaxPt
    /\ UNCHANGED <<Primary, Secondary, BlockedClient, Oplog, Store, Ot, OpCount,
                   ServerMsg, Pt>>
                   
ServerGetReply_majority ==
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = GET
        /\ InMsgs[s][1].rc = "major"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ Ot[s] >= InMsgs[s][1].ot
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] = 
            Append(@, [ op |-> GET, k |-> InMsgs[s][1].k, v |->
                        SnapshotTable[s][1][InMsgs[s][1].k], ct |-> Ct'[s], ot |-> Ot[s]])]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ Pt[s] + PtEpsilon <= MaxPt
    /\ UNCHANGED <<Primary, Secondary, BlockedClient, Oplog, Store, Ot, OpCount,
                   ServerMsg, Pt>>
                   
ServerGetReply_linearizable ==
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = GET
        /\ InMsgs[s][1].rc = "linea"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ Ot[s] >= InMsgs[s][1].ot
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] = 
            Append(@, [ op |-> GET, k |-> InMsgs[s][1].k, v |->
                        Store[s][InMsgs[s][1].k], ct |-> Ct'[s], ot |-> Ot[s]])]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ Pt[s] + PtEpsilon <= MaxPt
    /\ UNCHANGED <<Primary, Secondary, BlockedClient, Oplog, Store, Ot, OpCount,
                   ServerMsg, Pt>>                                      

ServerPutReply ==
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = PUT
        /\ Tick(s)
        /\ Ot' = [ Ot EXCEPT ![Primary] =  Ct'[Primary] ]
        /\ Store' = [ Store EXCEPT ![Primary][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ Oplog' = [ Oplog EXCEPT ![Primary] =
                    Append(@, <<InMsgs[s][1].k, InMsgs[s][1].v, Ot'[Primary]>>)]
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] =
                    Append(@, [ op |-> PUT, ct |-> Ct'[s], ot |-> Ot'[s]])]
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ Pt[s] + PtEpsilon <= MaxPt
        /\ ~ HLCLt(Cp[s], InMsgs[s][1].ct)
    /\ UNCHANGED <<Primary, Secondary, BlockedClient, OpCount, ServerMsg, Pt>>

\* client
ClientGetRequest_local ==
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> GET, rc |-> "local", c |-> c, k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, OpCount,
                   ServerMsg, Pt>>
                   
ClientGetRequest_majority ==                   
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> GET, c |-> c, rc |-> "major", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, OpCount,
                   ServerMsg, Pt>>
                   
ClientGetRequest_linearizable ==                   
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> GET, c |-> c, rc |-> "linea", k |-> k, ct |-> Ct[c], ot |-> Ot[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, OpCount,
                   ServerMsg, Pt>>
                   
ClientPutRequest_number ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = 
            Append(@, [ op |-> PUT, wc |-> 1, c |-> c, k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, OpCount,
                   ServerMsg, Pt>>  
                                                                           
ClientPutRequest_majority ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = 
            Append(@, [ op |-> PUT, wc |-> "major", c |-> c, k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, OpCount,
                   ServerMsg, Pt>>
                                   
ClientGetResponse ==
    /\ \E c \in Client:
        /\ OpCount[c] /= 0
        /\ Len(InMsgc[c]) /= 0
        /\ InMsgc[c][1].op = GET
        /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ct) ]
        /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ot) ]
        /\ Store' = [ Store EXCEPT ![c][InMsgc[c][1].k] = InMsgc[c][1].v ]
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                            THEN BlockedClient \ {c}
                            ELSE BlockedClient
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, InMsgs, ServerMsg, Pt>>

ClientPutResponse ==
    /\ \E c \in Client:
        /\ OpCount[c] /= 0
        /\ Len(InMsgc[c]) /= 0
        /\ InMsgc[c][1].op = PUT
        /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ct) ]
        /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ot) ]
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                            THEN BlockedClient \ {c}
                            ELSE BlockedClient
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, InMsgs, ServerMsg, Pt>>

\* next
Next == \/ ClientGetRequest_local
        \/ ClientGetRequest_majority
        \/ ClientGetRequest_linearizable        
        \/ ClientPutRequest_number
        \/ ClientPutRequest_majority
        \/ ClientGetResponse 
        \/ ClientPutResponse
        \/ ServerGetReply_local
        \/ ServerGetReply_majority
        \/ ServerGetReply_linearizable               
        \/ ServerPutReply
        \/ Replicate
        \/ NTPSync 
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ Snapshot
        
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Mon Jan 04 14:56:31 CST 2021 by JYwellin
\* Created Fri Mar 13 15:53:03 CST 2020 by JYwellin
