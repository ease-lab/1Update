--------------------------- MODULE OneUpdate ---------------------------
EXTENDS OneUpdateMeta

-------------------------------------------------------------------------------------
\* Helpers
dir_has_action_pending == dReqPending  = 1
dir_set_action_pending == dReqPending' = 1
dir_rst_action_pending == dReqPending' = 0

upd_dir_state(s) == dState' = s
upd_state(n, s)  == cState' = [cState EXCEPT![n] = s]

\* 
rmv_sharer(s) == dSharers' = dSharers \ {s}
add_sharer(s) == dSharers' = dSharers \union {s}


upd_owner(o) == 
    /\ dOwner'   = o  
    /\ dSharers' = {o}

rmv_owner(o) == 
    /\ rmv_sharer(o) 
    /\ dOwner' = EMPTY_OWNER
                
rst_acks(n) == 
    cRcvAcks' = [cRcvAcks EXCEPT![n] = {}]
add_ack(n, m) ==
    cRcvAcks' = [cRcvAcks EXCEPT![n] = cRcvAcks[n] \union {m.sender}]


rst_dir_acks == 
    dRcvAcks' = {}
add_dir_ack(m) == 
    dRcvAcks' = dRcvAcks \union {m.sender}

rcv_upd_ack_msg(n, m) == 
    /\ m.receiver = n
    /\ m.type = "UAck" 

rcv_ack_msg(n, m) == 
    /\ m.receiver = n
    /\ \/ m.type = "SAck" 
       \/ m.type = "SDataAck"


_is_last_Ack_from_set(n, m, set) == 
    set \subseteq (cRcvAcks[n] \union {m.sender})


is_last_Ack(n, m) == 
    /\ rcv_ack_msg(n, m)
    /\ _is_last_Ack_from_set(n, m, dSharers \ {n})

is_last_upd_Ack(n, m) == 
    /\ rcv_upd_ack_msg(n, m)
    /\ _is_last_Ack_from_set(n, m, CORES \ {n})

is_last_dir_Ack(m) == 
    /\ m.type = "UAck" 
    /\ dSharers \subseteq (dRcvAcks \union {m.sender})

owner_or_min_sharer == 
    IF dOwner # EMPTY_OWNER 
    THEN dOwner 
    ELSE Min(dSharers)

sharers_no_fwd == dSharers \ {owner_or_min_sharer}

-------------------------------------------------------------------------------------
\**********************************
\* Requests involving only Directory
\**********************************

\* Local write hit
EtoM(n) == \* E to M
    /\ cState[n] = "E"
    /\ upd_owner(n)
    /\ upd_state(n, "M")
    /\ upd_dir_state("M")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


\* Eviction
PutE(n) == \* E to I
    /\ cState[n] = "E"
    /\ rmv_owner(n)
    /\ upd_state(n, "I")
    /\ upd_dir_state("I")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


PutM(n) == \* M to I
    /\ cState[n] = "M"
    /\ rmv_owner(n)
    /\ upd_mem_data(n)
    /\ upd_state(n, "I")
    /\ upd_dir_state("I")
    /\ unchanged_gMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


PutS(n) == \* S to I/S
    /\ cState[n] = "S"
    /\ rmv_sharer(n)
    /\ upd_state(n, "I")
    /\ IF Cardinality(dSharers) = 1
       THEN upd_dir_state("I")
       ELSE UNCHANGED <<dState>>
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dOwner, dReqPending, cData, cRcvAcks, dRcvAcks>>


PutO(n) == \* O to I/S
    /\ cState[n] = "O"
    /\ rmv_owner(n)
    /\ upd_mem_data(n)
    /\ upd_state(n, "I")
    /\ IF Cardinality(dSharers) = 1
       THEN upd_dir_state("I")
       ELSE upd_dir_state("S")
    /\ unchanged_gMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


\* Cache miss (fetching from memory)
GetS_dI(n) == \* I to E
    /\ dState = "I"
    /\ cState[n] = "I"
    /\ add_sharer(n)
    /\ rd_mem_data(n)
    /\ upd_state(n, "E")
    /\ upd_dir_state("E")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dOwner, dReqPending, cRcvAcks, dRcvAcks>>

GetM_dI(n) == \* I to M
    /\ dState = "I"
    /\ cState[n] = "I"
    /\ upd_owner(n)
    /\ rd_mem_data(n)
    /\ upd_state(n, "M")
    /\ upd_dir_state("M")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cRcvAcks, dRcvAcks>>
    
-------------------------------------------------------------------------------------
\* Dir
GetS_Fwd(n) ==
    /\ dState # "I"
    /\ cState[n] = "I"
    /\ dir_set_action_pending 
    /\ ucst_FwdGetS(n, owner_or_min_sharer)
    /\ IF (dState = "E" \/ dState = "S")
       THEN /\ upd_dir_state("S")
       ELSE upd_dir_state("O")   
    /\ unchanged_gmc
    /\ UNCHANGED <<dOwner, dSharers, dRcvAcks>>

GetS(n) ==
    \/ GetS_dI(n)
    \/ GetS_Fwd(n)

\* Sharers
RcvFwdGetS(n, m) ==
    /\ rcv_FwdGetS(m, n)
    /\ resp_SData(m)
    /\ IF (cState[n] = "E" \/ cState[n] = "S")
       THEN upd_state(n, "S")
       ELSE upd_state(n, "O")   
    /\ unchanged_gmd
    /\ UNCHANGED <<cData, cRcvAcks, dRcvAcks>>

\* Requester
RcvData(n, m) ==
    /\ rcv_SData(m, n)
    /\ deliver_Msg(m)
    /\ add_sharer(n)
    /\ upd_state(n, "S")
    /\ upd_core_data(n, m.data)
    /\ dir_rst_action_pending 
    /\ unchanged_gm
    /\ UNCHANGED <<dOwner, dState, cRcvAcks, dRcvAcks>>
    
-------------------------------------------------------------------------------------
\* Dir
GetM_Invs(n) ==
    /\ dState # "I"
    /\ cState[n] # "M"
    /\ cState[n] # "E"
    /\ Cardinality(dSharers \ {n}) > 0
    /\ rst_acks(n)
    /\ dir_set_action_pending 
    /\ upd_dir_state("M")
    /\ unchanged_m
    /\ UNCHANGED <<dOwner, dSharers, cState, cData, dRcvAcks>>
    /\ IF (dState = "E" \/ dState = "M")
       THEN /\ ucst_FwdGetM(n, owner_or_min_sharer)     \* single remote owner case
            /\ unchanged_g
       ELSE IF (cState[n] = "S" \/ dOwner = n) 
            THEN /\ bcst_DInv(n, dSharers \ {n}) \* is owner but w/ sharers
                 /\ unchanged_Msgs
            ELSE /\ ucst_FwdGetM(n, owner_or_min_sharer) \* (remote) owner and sharers
                 /\ IF Cardinality(dSharers \ {owner_or_min_sharer, n}) > 0
                    THEN bcst_DInv(n, dSharers \ {owner_or_min_sharer, n})
                    ELSE unchanged_g

GetM(n) ==
    \/ EtoM(n) 
    \/ GetM_dI(n)
    \/ GetM_Invs(n)
      

\* Sharers -> rcvInv or FwdGetM
RcvInv(n, m) == 
    /\ (rcv_DInv(m, n) \/ rcv_FwdGetM(m, n))
    /\ upd_state(n, "I")
    /\ IF rcv_DInv(m, n)
           THEN resp_SAck(m)
           ELSE resp_SDataAck(m)
    /\ unchanged_gmd
    /\ UNCHANGED <<cData, cRcvAcks, dRcvAcks>>

\* Requester -> normal Ack or DataAck
RcvAck(n, m) == 
    /\ rcv_ack_msg(n, m)
    /\ deliver_Msg(m)
    /\ unchanged_gm
    /\ UNCHANGED <<dState, dRcvAcks>>
    /\ IF rcv_SDataAck(m, n)
       THEN upd_core_data(n, m.data)
       ELSE UNCHANGED <<cData>> 
    /\ IF ~is_last_Ack(n, m) 
       THEN /\ add_ack(n, m)
            /\ unchanged_d
            /\ UNCHANGED <<cState>>
       ELSE /\ rst_acks(n)
            /\ upd_owner(n)
            /\ upd_state(n, "M")
            /\ dir_rst_action_pending 

-------------------------------------------------------------------------------------
\* Dir
\*SharedUpdate

\*predicate
\* For simplicity now we always make every core a sharer here
MtoO(n) ==
    /\ dir_set_action_pending 
    /\ bcst_Upd(n, CORES \ {n}, cData[n])
    /\ unchanged_mMsgs 
    /\ IF ENABLE_DIR_ACKS 
       THEN /\ upd_state(n, "O") \* update eagerly to O state if dir collects ACKs
            /\ dRcvAcks = {n} \* add the requester to rcved acks for easier check of all acks predicate
       ELSE /\ rst_acks(n)
            /\ UNCHANGED <<cState, dRcvAcks>>
    /\ UNCHANGED <<cData, dOwner, dSharers, dState>>

RcvUpd(n, m) == 
    /\ rcv_Upd(m, n)
    /\ resp_UAck(m) 
    /\ upd_state(n, "S") 
    /\ upd_core_data(n, m.data)
    /\ unchanged_gmd
    /\ UNCHANGED <<cRcvAcks, dRcvAcks>>

RcvUpdAck(n, m) == 
    /\ ~ENABLE_DIR_ACKS 
    /\ cState[n] = "M"
    /\ rcv_upd_ack_msg(n, m)
    /\ deliver_Msg(m)
    /\ unchanged_gm
    /\ UNCHANGED <<cData, dRcvAcks>>
    /\ IF ~is_last_upd_Ack(n, m) 
       THEN /\ add_ack(n, m)
            /\ unchanged_d
            /\ UNCHANGED <<cState>>
       ELSE /\ rst_acks(n)
            /\ upd_state(n, "O")
            /\ dState'    = "O"
            /\ dOwner'    = n
            /\ dSharers'  = CORES
            /\ dir_rst_action_pending 


DirRcvUpdAck(m) == 
    /\ ENABLE_DIR_ACKS 
    /\ dir_has_action_pending 
    /\ dState = "M"
    /\ m.type = "UAck" 
    /\ deliver_Msg(m)
    /\ unchanged_gmc
    /\ UNCHANGED <<dOwner>>
    /\ IF ~is_last_dir_Ack(m)
       THEN /\ add_dir_ack(m) 
            /\ UNCHANGED <<dSharers, dReqPending, dState>>
       ELSE /\ rst_dir_acks
            /\ dState'    = "O"
            /\ dSharers'  = CORES
            /\ dir_rst_action_pending 

-------------------------------------------------------------------------------------
must_update(n) ==
    /\ cState[n] = "M"
    /\ cData[n]  = WRITE_TO_UPDATE


Requests(n) == 
    /\ ~dir_has_action_pending 
    /\ IF must_update(n)
       THEN MtoO(n)
       ELSE \/ GetM(n)
            \/ GetS(n)
            \/ PutE(n) 
            \/ PutM(n) 
            \/ PutS(n)
            \/ PutO(n)
       
SharerActions(n, m) == 
    \/ RcvUpd(n, m)
    \/ RcvInv(n, m)
    \/ RcvFwdGetS(n, m)

RequesterActions(n, m) == 
    \/ RcvAck(n, m)
    \/ RcvData(n, m)
    \/ RcvUpdAck(n, m)

DirActions(m) == DirRcvUpdAck(m)

MessageActions(n) ==
    \E m \in Msgs:
        \/ DirActions(m)
        \/ SharerActions(n, m)
        \/ RequesterActions(n, m)

PerformBcast ==
        /\ gBcstMsg # {}
        /\ \E m \in gBcstMsg:
           /\ _send_Msg(m)
           /\ unchanged_mcd
           /\ UNCHANGED <<dRcvAcks>>
           /\ IF gBcstMsgRcvers = {}
              THEN /\ gBcstMsg' = {} 
                   /\ UNCHANGED <<gBcstMsgRcvers>>
              ELSE LET rcver == CHOOSE x \in gBcstMsgRcvers : TRUE IN 
                   /\ gBcstMsg' = {[m EXCEPT!.receiver = rcver]}
                   /\ gBcstMsgRcvers' = gBcstMsgRcvers \ {rcver}
 
-------------------------------------------------------------------------------------
WriteData(n) == 
    /\ cState[n] = "M"
    /\ cData[n] < MAX_WRITES
    /\ ~must_update(n)
    /\ cData' = [cData EXCEPT![n] = cData[n] + 1]
    /\ unchanged_gdmMsgs 
    /\ UNCHANGED <<cState, cRcvAcks, dRcvAcks>>

\* Modeling 1-Update protocol (Directory, memory and core/cache actions)
ANext == 
        IF   gBcstMsg # {}
        THEN PerformBcast 
        ELSE \E n \in CORES:
             \/ Requests(n) 
             \/ WriteData(n)
             \/ MessageActions(n)
(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == AInit /\ [][ANext]_vars

Invariants == /\ ([]ATypeOK) /\ ([]INVARIANTS)


THEOREM Spec => Invariants
=============================================================================
