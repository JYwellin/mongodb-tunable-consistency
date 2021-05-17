------------------------------ MODULE TunableMongoDB ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* constants and variables
CONSTANTS Client, Server,   \* the set of clients and servers
          Key, Value,      \* the set of keys and values
          Nil,            \* model value, place holder
          OpTimes,        \* op count at most
          PtStop,          \* max physical time
          Number            \* writeConcern number

VARIABLES Primary,        \* Primary node
          Secondary,      \* secondary nodes
          Oplog,          \* oplog[s]: oplog at server[s]
          Store,          \* store[s]: data stored at server[s]
          Ct,             \* Ct[s]: cluster time at node s
          Ot,             \* Ot[s]: the last applied operation time at server s
          InMsgc,         \* InMsgc[c]: the channel of messages at client c \in Client
          InMsgs,         \* InMsgc[s]: the channel of messages at server s \in Server
          ServerMsg,      \* ServerMsg[s]: the channel of heartbeat msgs at server s
          BlockedClient,  \* BlockedClient: Client operations in progress
          BlcokedThread,  \* BlcokedThread: blocked user thread and content
          OpCount,        \* OpCount[c]: op count for client c
          Pt,             \* Pt[s]: physical time at server s
          Cp,             \* Cp[s]: majority commit point at server s
          State,          \* State[s]: the latest Ot of all servers that server s knows
          CalState,       \* CalState: sorted State[Primary]         
          SnapshotTable,  \* SnapshotTable[s] : snapshot mapping table at server s
          History         \* History[c]: History sequence at client c
-----------------------------------------------------------------------------
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

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, ServerMsg, BlockedClient, BlcokedThread, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>

RECURSIVE CreateState(_,_) \* init state
CreateState(len, seq) == IF len = 0 THEN seq
                         ELSE CreateState(len - 1, Append(seq, [ p |-> 0, l |-> 0 ]))
                       
-----------------------------------------------------------------------------
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
InitBlcokedThread == BlcokedThread = [s \in Client |-> Nil ] 
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitCalState == CalState = CreateState(Cardinality(Server), <<>>)
                             \* create initial state(for calculate)
InitState == State = [ s \in Server |-> [ s0 \in Server |-> 
                                              [ p |-> 0, l |-> 0 ] ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> Nil] ] >>]  
InitHistory == History = [c \in Client |-> <<>>]  \* History operation seq is empty                                                                                       

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitCp /\ InitCalState /\ InitInMsgc /\ InitInMsgs 
    /\ InitServerMsg /\ InitBlockedClient /\ InitBlcokedThread /\ InitOpCount
    /\ InitState /\ InitSnap /\ InitHistory
-----------------------------------------------------------------------------
\* snapshot
RECURSIVE SelectSnapshot_rec(_, _, _)
SelectSnapshot_rec(stable, cp, index) ==
    IF HLCLt(cp, stable[index].ot) THEN stable[index - 1].store
    ELSE IF index = Len(stable) THEN stable[index].store
    ELSE SelectSnapshot_rec(stable, cp, index + 1)
    
SelectSnapshot(stable, cp) == SelectSnapshot_rec(stable, cp, 1)

\* snapshot periodly
-----------------------------------------------------------------------------

Snapshot == 
    /\ \E s \in Server:
            SnapshotTable' =  [ SnapshotTable EXCEPT ![s] = 
                                Append(@, [ot |-> Ot[s], store |-> Store[s] ]) ]  
                               \* create a new snapshot
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, 
                   InMsgs, ServerMsg, BlockedClient, BlcokedThread,
                   OpCount, Pt, Cp, CalState, State, History>>                          

-----------------------------------------------------------------------------
                                      
\* commit point
RECURSIVE AddState(_,_,_)
AddState(new, state, index) == IF index = 1 /\ HLCLt(new, state[1]) THEN  <<new>> \o state\* less than the first 
                               ELSE IF index = Len(state) + 1 THEN state \o <<new>>
                               ELSE IF HLCLt(new, state[index]) THEN SubSeq(state, 1, index - 1) \o <<new>> \o SubSeq(state, index, Len(state))
                               ELSE AddState(new, state, index + 1)
RECURSIVE RemoveState(_,_,_) 
RemoveState(old, state, index) == IF state[index] = old THEN SubSeq(state, 1, index - 1) \o SubSeq(state, index + 1, Len(state))
                                  ELSE RemoveState(old, state, index + 1)

AdvanceState(new, old, state) == AddState(new, RemoveState(old, state, 1), 1)

AdvanceCp == 
    /\ Cp' = [Cp EXCEPT ![Primary] = CalState[Cardinality(Server) \div 2 + 1] ] 
    /\ UNCHANGED<<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, ServerMsg, BlockedClient, BlcokedThread, OpCount, Pt, CalState, State, SnapshotTable,History>> 
                   
\* heartbeat
BroadcastHeartbeat(s) == 
    LET msg == [ s |-> s, aot |-> Ot[s], ct |-> Ct[s], cp |-> Cp[s] ]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]   
                                                                                                                                                                                        
ServerTakeHeartbeat ==
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![ServerMsg[s][1].s] = 
                        ServerMsg[s][1].aot ]
            IN [ State EXCEPT ![s] = hb]
        /\ CalState' = LET newcal ==   
                       IF s = Primary \* primary node: update CalState
                       THEN  AdvanceState(ServerMsg[s][1].aot, 
                                       State[s][ServerMsg[s][1].s], CalState) 
                       ELSE CalState  IN newcal
        /\ Cp' = LET newcp ==
                 \* primary node: compute new mcp
                 IF s = Primary THEN CalState'[Cardinality(Server) \div 2 + 1]
                 \* secondary node: update mcp   
                 ELSE IF ~ HLCLt(ServerMsg[s][1].cp, Cp[s])
                      /\ ~ HLCLt(Ot[s], ServerMsg[s][1].cp)
                 THEN ServerMsg[s][1].cp
                 ELSE Cp[s]
                 IN [ Cp EXCEPT ![s] = newcp ]
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]         
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ot, InMsgc, InMsgs, 
         BlockedClient, BlcokedThread, OpCount, Pt, SnapshotTable, History>>


    
\* clock

UnchangedExPt == <<Primary, Secondary, InMsgc, InMsgs, ServerMsg, Oplog, Store,
                   Ct, Ot, BlockedClient, OpCount>>
UnchangedExCt == <<Primary, Secondary, InMsgc, InMsgs, ServerMsg, Oplog, Store,
                   Pt, Ot, BlockedClient, OpCount>>

MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] IN Pt[x]

NTPSync == \* simplify NTP protocal
    /\ Pt' = [ s \in Server |-> MaxPt ] 
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, 
                  ServerMsg, BlockedClient, BlcokedThread, OpCount, Cp,
                  CalState, State, SnapshotTable, History>>

AdvancePt == 
     \E s \in Server:  
           /\ s = Primary                    \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, InMsgs, State, 
       BlockedClient, BlcokedThread, OpCount, Cp, CalState, SnapshotTable, History>>

Tick(s) == Ct' = IF Ct[s].p >= Pt[s] THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]

\* Replicate

ReplicateOplog(s) == LET len_s == Len(Oplog[s])
                         len_p == Len(Oplog[Primary])
                     IN IF s /= Primary /\ len_s < len_p
                        THEN SubSeq(Oplog[Primary], len_s + 1, len_p)
                        ELSE <<>>
                       
Replicate ==
    /\ \E s \in Secondary:
        /\ ReplicateOplog(s) /= <<>>
        /\ Oplog' = [ Oplog EXCEPT ![s] = @ \o ReplicateOplog(s) ]
        /\ Store' = [ Store EXCEPT ![s] = Store[Primary] ]
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], Ct[Primary]) ] \*update Ct[s]
        /\ Ot' = [ Ct EXCEPT ![s] = HLCMax(Ot[s], Ot[Primary]) ] \*update Ot[s]
        /\ Cp' = [ Cp EXCEPT ![s] = HLCMax(Cp[s], Cp[Primary]) ] \*update Cp[s]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot[Primary] ]
            IN [ State EXCEPT ![s] = hb] \* update primary state s knows
        /\ LET msg == [ s |-> s, aot |-> Ot'[s], ct |-> Ct'[s], cp |-> Cp'[s] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![Primary] 
                              = Append(ServerMsg[Primary], msg) ]
           \* we treat replSetUpdatePosition as a special heartbeat
        /\ UNCHANGED<<Primary, Secondary, InMsgc, InMsgs, BlockedClient, 
                  BlcokedThread, OpCount, Pt, CalState, SnapshotTable, History>>
        
\* server get
ServerGetReply_local ==
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0        \* message channel is not empty
        /\ InMsgs[s][1].op = "get"    \* msg type: get
        /\ InMsgs[s][1].rc = "local"  \* Read Concern: local
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] = 
            Append(@, [ op |-> "get", k |-> InMsgs[s][1].k, v |->
                        Store[s][InMsgs[s][1].k], ct |-> Ct'[s], ot |-> Ot[s]])]
            \* send msg to client            
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ot, ServerMsg,
                   BlockedClient, BlcokedThread, OpCount, Pt, Cp, 
                   CalState, State, SnapshotTable, History>>
                               
ServerGetReply_majority ==
    /\ \E s \in Server:
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "get"   \* msg type: get
        /\ InMsgs[s][1].rc = "major" \* Read Concern: majority
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], InMsgs[s][1].ct) ]
        /\ InMsgc' = [ InMsgc EXCEPT ![InMsgs[s][1].c] = 
            Append(@, [ op |-> "get", k |-> InMsgs[s][1].k, v |-> 
                        SelectSnapshot(SnapshotTable[s], Cp[s])[InMsgs[s][1].k], ct
                        |-> Ct'[s], ot |-> Cp[s]])]
            \* send msg to client  
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
    /\ UNCHANGED<<Primary, Secondary, Oplog, Store, Ot, ServerMsg,
                  BlockedClient, BlcokedThread, OpCount, Pt, Cp,
                  CalState, State, SnapshotTable, History>>
          
ServerGetReply_linearizable_sleep ==
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = "get"
        /\ InMsgs[s][1].rc = "linea" \* Read Concern: linearizable
        /\ Tick(s)  \* advance cluster time
        /\ Oplog' = [ Oplog EXCEPT ![Primary] =
                    Append(@, <<Nil, Nil, Ct'[s]>>)]
                    \* append noop operation to oplog[s]
        /\ Ot' = [ Ot EXCEPT ![s] =  Ct'[s] ] 
                    \* advance the last applied operation time Ot[s]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot'[Primary] ]
            IN [ State EXCEPT ![s] = hb] \* update primary state
        /\ CalState' = AdvanceState(Ot'[Primary], Ot[Primary], CalState)                     
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]
        /\ BlcokedThread' = [BlcokedThread EXCEPT ![InMsgs[s][1].c] = 
                            [type |-> "read_linea", ot|-> Ct'[s], s |-> s, k 
                            |->InMsgs[s][1].k, v |-> Store[s][InMsgs[s][1].k] ] ] 
                     \* add the user thread to BlcokedThread[c]                             
    /\ UNCHANGED <<Primary, Secondary, Store, InMsgc, ServerMsg, BlockedClient, 
                   OpCount, Pt, Cp, SnapshotTable, History>> 
                  
ServerGetReply_linearizable_wake ==
      /\ \E c \in Client:
        /\ BlcokedThread[c] /= Nil
        /\ BlcokedThread[c].type = "read_linea"
        /\  ~ HLCLt(Cp[BlcokedThread[c].s], BlcokedThread[c].ot) \* cp[s] >= target ot     
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Append(@, [ op |-> "get", k 
                       |-> BlcokedThread[c].k, v |-> BlcokedThread[c].v, ct
                       |-> Ct[BlcokedThread[c].s], ot|->BlcokedThread[c].ot ])] 
        /\ BlcokedThread' =  [ BlcokedThread EXCEPT ![c] = Nil ] \* remove blocked state
      /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgs, 
                     ServerMsg, BlockedClient, OpCount, Pt, Cp, 
                     CalState, State, SnapshotTable, History>> 
                      
\* server put

ServerPutReply_zero ==
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "put"   \* msg type: put
        /\ InMsgs[s][1].wc = "zero"  \* Write Concern: 0
        /\ Tick(s)                   \* advance cluster time
        /\ Ot' = [ Ot EXCEPT ![Primary] =  Ct'[Primary] ]
                         \* advance the last applied operation time Ot[Primary]
        /\ Store' = [ Store EXCEPT ![Primary][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ Oplog' = [ Oplog EXCEPT ![Primary] =
                    Append(@, <<InMsgs[s][1].k, InMsgs[s][1].v, Ot'[Primary]>>)]
                    \* append operation to oplog[primary]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot'[Primary] ]
            IN [ State EXCEPT ![s] = hb] \* update primary state
        /\ CalState' = AdvanceState(Ot'[Primary], Ot[Primary], CalState)                   
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@)]      
    /\ UNCHANGED <<Primary, Secondary, InMsgc, ServerMsg, BlockedClient, 
                BlcokedThread, OpCount, Pt, Cp, SnapshotTable, History>>
----------------------------------------------------------------------------- 
    
ServerPutReply_number_sleep ==
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0       \* message channel is not empty
        /\ InMsgs[s][1].op = "put"   \* msg type: put
        /\ InMsgs[s][1].wc = "num"   \* Write Concern: num
        /\ Tick(s)                   \* advance cluster time
        /\ Ot' = [ Ot EXCEPT ![Primary] =  Ct'[Primary] ]
                         \* advance the last applied operation time Ot[Primary]
        /\ Store' = [ Store EXCEPT ![Primary][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ Oplog' = [ Oplog EXCEPT ![Primary] =
                    Append(@, <<InMsgs[s][1].k, InMsgs[s][1].v, Ot'[Primary]>>)]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot'[Primary] ]
            IN [ State EXCEPT ![s] = hb] \* update primary state
        /\ CalState' = AdvanceState(Ot'[Primary], Ot[Primary], CalState)                
        /\ BlcokedThread' = [BlcokedThread EXCEPT ![InMsgs[s][1].c] = [type 
            |-> "write_num", ot |-> Ct'[s], s |-> s, numnode |-> InMsgs[s][1].num] ] 
                      \* add the user thHistory to BlcokedThread[c]            
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]         
    /\ UNCHANGED <<Primary, Secondary, InMsgc, ServerMsg, BlockedClient, 
                   OpCount, Pt, Cp, SnapshotTable, History>>
                      
 
ServerPutReply_number_wake ==     
      /\ \E c \in Client:
        /\ BlcokedThread[c] /=  Nil
        /\ BlcokedThread[c].type = "write_num"
        /\  ~ HLCLt(CalState[Cardinality(Server) - BlcokedThread[c].numnode + 1],
                    BlcokedThread[c].ot)  \* CalState[s][n- num + 1] >= target ot
        /\ InMsgc' = [ InMsgc EXCEPT ![c] =  Append(@, [ op |-> "put", ct 
                       |-> Ct[Primary], ot |-> BlcokedThread[c].ot]) ] 
        /\ BlcokedThread' =  [ BlcokedThread EXCEPT ![c] = Nil ] 
                                                       \* remove blocked state
      /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgs, 
                     ServerMsg, BlockedClient, OpCount, Pt, Cp, 
                     CalState, State, SnapshotTable, History>>
       
ServerPutReply_majority_sleep == 
    /\ \E s \in Server:
        /\ s = Primary
        /\ Len(InMsgs[s]) /= 0
        /\ InMsgs[s][1].op = "put"
        /\ InMsgs[s][1].wc = "major"        
        /\ Tick(s)
        /\ Ot' = [ Ot EXCEPT ![Primary] =  Ct'[Primary] ]
        /\ Store' = [ Store EXCEPT ![Primary][InMsgs[s][1].k] = InMsgs[s][1].v ]
        /\ Oplog' = [ Oplog EXCEPT ![Primary] =
                    Append(@, <<InMsgs[s][1].k, InMsgs[s][1].v, Ot'[Primary]>>)]
        /\ State' = 
            LET SubHbState == State[s]
                hb == [ SubHbState EXCEPT ![Primary] = Ot'[Primary] ]
            IN [ State EXCEPT ![s] = hb] \* update primary state
        /\ CalState' = AdvanceState(Ot'[Primary], Ot[Primary], CalState)                       
        /\ BlcokedThread' = [BlcokedThread EXCEPT ![InMsgs[s][1].c] = [type |-> "write_major", ot
                     |-> Ct'[s], s |-> s ] ]               
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Tail(@) ]       
    /\ UNCHANGED <<Primary, Secondary, InMsgc, ServerMsg, BlockedClient, OpCount, Pt, Cp, SnapshotTable, History>>
    
ServerPutReply_majority_wake ==    
      /\ \E c \in Client:
        /\ BlcokedThread[c] /=  Nil        
        /\ BlcokedThread[c].type = "write_major"
        /\  ~ HLCLt(Cp[Primary], BlcokedThread[c].ot)      
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = 
            Append(@, [ op |-> "put", ct |-> Ct[BlcokedThread[c].s ]]) ]  
        /\ BlcokedThread' =  [ BlcokedThread EXCEPT ![c] = Nil ]  
      /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgs, ServerMsg, BlockedClient, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>  
                
\* client get
----------------------------------------------------------------------------- 

ClientGetRequest_local_primary ==
    /\ \E k \in Key, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "local", k |-> k, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg,
                   BlcokedThread, OpCount, Pt, Cp, CalState, 
                   State, SnapshotTable, History>>

ClientGetRequest_local_secondary ==
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Secondary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "local", k |-> k, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, BlcokedThread, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>
                       
ClientGetRequest_majority_primary ==                   
    /\ \E k \in Key, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "major", k |-> k, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, BlcokedThread, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>

ClientGetRequest_majority_secondary ==                   
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Secondary:
        /\ InMsgs' = [ InMsgs EXCEPT ![s] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "major", k |-> k, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, BlcokedThread, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>
                       
ClientGetRequest_linearizable ==                   
    /\ \E k \in Key, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = Append(@,
            [ op |-> "get", c |-> c, rc |-> "linea", k |-> k, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED  <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, BlcokedThread, OpCount, Pt, Cp, CalState, State, SnapshotTable, History>>
    
\* client put    
ClientPutRequest_zero ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient:
        /\ OpCount[c] /= 0
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "zero", k
                       |-> k, v |-> v, ct |-> Ct[c]])]
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]    
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc,
                   ServerMsg, BlockedClient, BlcokedThread, Pt, Cp, 
                   CalState, State, SnapshotTable, History>>
                   
ClientPutRequest_number ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, num \in Number:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "num", num |-> num, k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<OpCount, Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, 
                   BlcokedThread, Pt, Cp, CalState, State, SnapshotTable, History>> 
                                                                           
ClientPutRequest_majority ==
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient:
        /\ InMsgs' = [ InMsgs EXCEPT ![Primary] = 
            Append(@, [ op |-> "put", c |-> c, wc |-> "major", k |-> k, v |-> v, ct |-> Ct[c]])]
        /\ BlockedClient' = BlockedClient \cup {c}
    /\ UNCHANGED <<OpCount, Primary, Secondary, Oplog, Store, Ct, Ot, InMsgc, ServerMsg, BlcokedThread, Pt, Cp, CalState, State, SnapshotTable, History>>

                                   
ClientGetResponse ==
    /\ \E c \in Client:
        /\ OpCount[c] /= 0          \* client c has operation times
        /\ Len(InMsgc[c]) /= 0      \* message channel is not empty
        /\ InMsgc[c][1].op = "get"  \* msg type: get
        /\ Store' = [ Store EXCEPT ![c][InMsgc[c][1].k] = InMsgc[c][1].v ] 
            \* store data
        /\ History' = [History EXCEPT ![c] = Append(@, [ op 
                        |-> "get", ts |-> InMsgc[c][1].ot ]) ]    
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                            THEN BlockedClient \ {c}
                            ELSE BlockedClient  \* remove blocked state
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Ct, Ot, InMsgs, ServerMsg, 
                   BlcokedThread, Pt, Cp, CalState, State, SnapshotTable>>


ClientPutResponse ==
    /\ \E c \in Client:
        /\ OpCount[c] /= 0          \* client c has operation times
        /\ Len(InMsgc[c]) /= 0      \* message channel is not empty
        /\ InMsgc[c][1].op = "put"  \* msg type: put
        /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, InMsgc[c][1].ct) ]
        /\ History' = [History EXCEPT ![c] = Append(@, [ op 
                        |-> "put", ts |-> InMsgc[c][1].ot ]) ]         
        /\ InMsgc' = [ InMsgc EXCEPT ![c] = Tail(@) ]
        /\ BlockedClient' = IF Len(InMsgc'[c]) = 0
                            THEN BlockedClient \ {c}
                            ELSE BlockedClient  \* remove blocked state
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
    /\ UNCHANGED <<Primary, Secondary, Oplog, Store, Ot, InMsgs, ServerMsg,
                   BlcokedThread, Pt, Cp, CalState, State, SnapshotTable>>
                   



ClientGetRequest_local == \/ ClientGetRequest_local_primary 
                          \/ ClientGetRequest_local_secondary
ClientGetRequest_majority == \/ ClientGetRequest_majority_primary 
                             \/ ClientGetRequest_majority_secondary

\* all possible client get actions      
ClientGetRequest == \/ ClientGetRequest_local 
                    \/ ClientGetRequest_majority 
                    \/ ClientGetRequest_linearizable

\* all possible clent put actions                          
ClientPutRequest == \/ ClientPutRequest_zero
                    \/ ClientPutRequest_number
                    \/ ClientPutRequest_majority

\* all possible server get actions                     
ServerGetReply == \/ ServerGetReply_local 
                  \/ ServerGetReply_majority 
                  \/ ServerGetReply_linearizable_sleep
                  \/ ServerGetReply_linearizable_wake  

\* all possible server put actions                 
ServerPutReply == \/ ServerPutReply_zero 
                  \/ ServerPutReply_number_sleep 
                  \/ ServerPutReply_majority_sleep
                  \/ ServerPutReply_number_wake  
                  \/ ServerPutReply_majority_wake
                  
                  
                  
-----------------------------------------------------------------------------
                  
\* next state for all configurations
Next == \/ ClientGetRequest \/ ClientPutRequest
        \/ ClientGetResponse \/ ClientPutResponse
        \/ ServerGetReply \/ ServerPutReply
        \/ Replicate 
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ Snapshot
        
Spec == Init /\ [][Next]_vars       
 
Next_Except_ClientRequset == \/ ClientGetResponse
                             \/ ClientPutResponse
                             \/ ServerGetReply        
                             \/ ServerPutReply
                             \/ Replicate 
                             \/ AdvancePt
                             \/ ServerTakeHeartbeat
                             \/ Snapshot
                             
ClientRequset_1 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_local_primary  

ClientRequset_2 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_local_secondary 

ClientRequset_3 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_majority_primary

ClientRequset_4 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_majority_secondary

ClientRequset_5 == \/ ClientPutRequest_majority   
                   \/ ClientGetRequest_linearizable

ClientRequset_6 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_local_primary  

ClientRequset_7 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_local_secondary 

ClientRequset_8 == \/ ClientPutRequest_number   
                   \/ ClientGetRequest_majority_primary

ClientRequset_9 == \/ ClientPutRequest_number  
                   \/ ClientGetRequest_majority_secondary

ClientRequset_10 == \/ ClientPutRequest_number  
                    \/ ClientGetRequest_linearizable          
                   
Next1 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_1

Next2 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_2

Next3 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_3

Next4 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_4
         
Next5 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_5

Next6 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_6

Next7 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_7

Next8 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_8        
         
Next9 == \/ Next_Except_ClientRequset 
         \/ ClientRequset_9  
  
Next10 == \/ Next_Except_ClientRequset 
          \/ ClientRequset_10                                                                                                                                                                                                    
                
Spec1 == Init /\ [][Next1]_vars
Spec2 == Init /\ [][Next2]_vars
Spec3 == Init /\ [][Next3]_vars
Spec4 == Init /\ [][Next4]_vars
Spec5 == Init /\ [][Next5]_vars
Spec6 == Init /\ [][Next6]_vars
Spec7 == Init /\ [][Next7]_vars
Spec8 == Init /\ [][Next8]_vars
Spec9 == Init /\ [][Next9]_vars
Spec10 == Init /\ [][Next10]_vars

MonotonicRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "get"
                    /\ History[c][j].op = "get"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)
   
MonotonicWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "put"
                    /\ History[c][j].op = "put"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)                             
=============================================================================
\* Modification History
\* Last modified Mon May 17 21:53:21 CST 2021 by JYwellin
\* Created Fri Mar 13 15:53:03 CST 2020 by JYwellin
