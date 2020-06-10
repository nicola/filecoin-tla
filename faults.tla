---- MODULE faults ----
EXTENDS Integers, TLC

CONSTANTS Miners, SectorIDs, SectorStates, WpostFlags

\* Faults
ZERO == "0"
FF == "ff"
SP == "sp"
TF == "tf"
PreCommitDeposit == "pcd"

\* errors
NOERROR == "no sectorStateError"

\* Sector State transitions
NULLSTATE == "null state"

NULLFLAG == "null flag"

(*--algorithm faults
variables
    sectorState \in SectorStates,
    wpostFlag = NULLFLAG,
    failedPoSts \in 1..2,
    skippedFault \in BOOLEAN,
    nextState = NULLSTATE,
    penalties = ZERO,
    sectorStateError = NOERROR;

define
    SectorStateTransitions == {
        \* Honest transitions
        <<"null", "precommit", {ZERO}>>,
        <<"precommit", "active", {ZERO}>>,
    
        \* Faults
        <<"active", "faulty", {FF, SP}>>,
        <<"faulty", "active", {ZERO}>>,

        \* sectors are terminated
        \* <<"faulty", "done", {FF, SP, TF}>>,
        \* <<"active", "done", {ZERO, TF}>>,

        \* Sector is cleaned up, ID can be reused
        <<"precommit", "null", {PreCommitDeposit}>>
    }
    SectorStateTransition(from, to) == <<from, to>> \in { <<x[1], x[2]>> : x \in SectorStateTransitions }

    SectorStateTransitionInvariant == LET
        \* A valid state transition has no sectorStateError
        ValidStateTs == SectorStateTransition(sectorState, nextState) /\ sectorStateError = NOERROR
        \* An invalid state transition has an sectorStateError
        InvalidStateTsHaveError == ~SectorStateTransition(sectorState, nextState) /\ sectorStateError /= NOERROR
        \* Initial state
        InitTs == nextState = NULLSTATE /\ sectorStateError = NOERROR
    IN ValidStateTs \/ InvalidStateTsHaveError \/ InitTs

    ValidPoStTransitionInvariant == LET 
        WpostTs == {
            \* Flags for PoSts
            <<"active", "faulted", "faulty">>,
            <<"faulty", "recovered", "active">>,
            <<"faulty", "faulted", NULLSTATE>>
        }
        WpostValidFlags(from, flag) == <<from, flag>> \in { <<x[1], x[2]>> : x \in WpostTs }
        WpostValidTs(from, flag, to) == <<from, flag, to>> \in WpostTs
        ValidFlagsBeforePoSt == sectorState \in {"active", "faulty"} /\ nextState = NULLSTATE /\ wpostFlag /= NULLFLAG => WpostValidFlags(sectorState, wpostFlag)
        ValidFlagsAfterPoSt == sectorState \in {"active", "faulty"} /\ nextState /= NULLSTATE /\ wpostFlag /= NULLFLAG => WpostValidTs(sectorState, wpostFlag, nextState)
        InitTs == nextState = NULLSTATE /\ sectorStateError = NOERROR
    IN (ValidFlagsBeforePoSt /\ ValidFlagsAfterPoSt) \/ InitTs

end define;

fair+ process miner = "miner"
variables epoch = 0
begin
    Blockchain:
        while epoch < 3 do
            epoch := epoch + 1;
            Block:
                either
                    PreCommit:
                        if sectorState /= "null" then
                            sectorStateError := "invalid precommit";
                        else
                            \* Mark sector as committed
                            nextState := "precommit";
                        end if;
                or
                    Commit:
                        if sectorState /= "precommit" then
                            sectorStateError := "invalid commit";
                        else
                            \* Mark sector as active
                            nextState := "active";
                        end if;   
                or
                    DeclareFault:
                        if sectorState \in {"active", "faulty"} then
                            \* Flag active sector
                            wpostFlag := "faulted";
                        else
                            sectorStateError := "invalid declare fault";
                        end if;
                or
                    DeclareRecovery:
                        if sectorState = "faulty" then
                            wpostFlag := "recovered";
                        else
                            sectorStateError := "invalid declare fault";
                        end if;
                or
                    WindowPoSt:
                        if sectorState \in {"active", "faulty"} then
                            \* State changes
                            \* Active -> Faulty: SkippedFault
                            if sectorState = "active" /\ wpostFlag = NULLFLAG /\ skippedFault then
                                nextState := "faulty";
                            \* Active -> Faulty: DeclareFault
                            elsif sectorState = "active" /\ wpostFlag = "faulted" then
                                nextState := "faulty";
                            \* Faulty -> Active: DeclareRecovery TODO
                            elsif sectorState = "faulty" /\ wpostFlag = "recovered" /\ ~skippedFault then
                                nextState := "active";
                            else
                                skip;
                            end if;
                            
                            \* Update faults counter when the sector is faulty
                            \* either the sector is faulty already
                            \*     or the sector is found to be faulty
                            if (sectorState = "faulty" /\ nextState = NULLSTATE) \/ nextState = "faulty" then
                                failedPoSts := failedPoSts + 1;
                            else
                                failedPoSts := 0;
                            end if;

                            \* Apply penalties
                            if failedPoSts > 3 then
                                penalties := TF;
                            elsif sectorState = "faulty" /\ wpostFlag = "recovered" /\ skippedFault then
                                penalties := SP;
                            elsif nextState = "faulty" then
                                penalties := SP;
                            elsif sectorState = "faulty" \/ (sectorState = "active" /\ wpostFlag = "faulted") then
                                penalties := FF;
                            end if;
                        end if;

                        WindowPoStReset:
                            wpostFlag := NULLFLAG;

                        \* Termination
                end either;
                Reset:
                    if nextState /= NULLSTATE then
                        sectorState := nextState
                    end if;
                    nextState := NULLSTATE;
                    penalties := ZERO;
                    sectorStateError := NOERROR;
                    with x \in BOOLEAN  do
                        skippedFault := x 
                    end with; 
                    
                    
        end while;
end process;

end algorithm; *)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9682627baa4f65175bd87b6d36bfb8d4
VARIABLES sectorState, wpostFlag, failedPoSts, skippedFault, nextState, 
          penalties, sectorStateError, pc

(* define statement *)
SectorStateTransitions == {

    <<"null", "precommit", {ZERO}>>,
    <<"precommit", "active", {ZERO}>>,


    <<"active", "faulty", {FF, SP}>>,
    <<"faulty", "active", {ZERO}>>,






    <<"precommit", "null", {PreCommitDeposit}>>
}
SectorStateTransition(from, to) == <<from, to>> \in { <<x[1], x[2]>> : x \in SectorStateTransitions }

SectorStateTransitionInvariant == LET

    ValidStateTs == SectorStateTransition(sectorState, nextState) /\ sectorStateError = NOERROR

    InvalidStateTsHaveError == ~SectorStateTransition(sectorState, nextState) /\ sectorStateError /= NOERROR

    InitTs == nextState = NULLSTATE /\ sectorStateError = NOERROR
IN ValidStateTs \/ InvalidStateTsHaveError \/ InitTs

ValidPoStTransitionInvariant == LET
    WpostTs == {

        <<"active", "faulted", "faulty">>,
        <<"faulty", "recovered", "active">>,
        <<"faulty", "faulted", NULLSTATE>>
    }
    WpostValidFlags(from, flag) == <<from, flag>> \in { <<x[1], x[2]>> : x \in WpostTs }
    WpostValidTs(from, flag, to) == <<from, flag, to>> \in WpostTs
    ValidFlagsBeforePoSt == sectorState \in {"active", "faulty"} /\ nextState = NULLSTATE /\ wpostFlag /= NULLFLAG => WpostValidFlags(sectorState, wpostFlag)
    ValidFlagsAfterPoSt == sectorState \in {"active", "faulty"} /\ nextState /= NULLSTATE /\ wpostFlag /= NULLFLAG => WpostValidTs(sectorState, wpostFlag, nextState)
    InitTs == nextState = NULLSTATE /\ sectorStateError = NOERROR
IN (ValidFlagsBeforePoSt /\ ValidFlagsAfterPoSt) \/ InitTs

VARIABLE epoch

vars == << sectorState, wpostFlag, failedPoSts, skippedFault, nextState, 
           penalties, sectorStateError, pc, epoch >>

ProcSet == {"miner"}

Init == (* Global variables *)
        /\ sectorState \in SectorStates
        /\ wpostFlag = NULLFLAG
        /\ failedPoSts \in 1..2
        /\ skippedFault \in BOOLEAN
        /\ nextState = NULLSTATE
        /\ penalties = ZERO
        /\ sectorStateError = NOERROR
        (* Process miner *)
        /\ epoch = 0
        /\ pc = [self \in ProcSet |-> "Blockchain"]

Blockchain == /\ pc["miner"] = "Blockchain"
              /\ IF epoch < 3
                    THEN /\ epoch' = epoch + 1
                         /\ pc' = [pc EXCEPT !["miner"] = "Block"]
                    ELSE /\ pc' = [pc EXCEPT !["miner"] = "Done"]
                         /\ epoch' = epoch
              /\ UNCHANGED << sectorState, wpostFlag, failedPoSts, 
                              skippedFault, nextState, penalties, 
                              sectorStateError >>

Block == /\ pc["miner"] = "Block"
         /\ \/ /\ pc' = [pc EXCEPT !["miner"] = "PreCommit"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "Commit"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "DeclareFault"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "DeclareRecovery"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "WindowPoSt"]
         /\ UNCHANGED << sectorState, wpostFlag, failedPoSts, skippedFault, 
                         nextState, penalties, sectorStateError, epoch >>

PreCommit == /\ pc["miner"] = "PreCommit"
             /\ IF sectorState /= "null"
                   THEN /\ sectorStateError' = "invalid precommit"
                        /\ UNCHANGED nextState
                   ELSE /\ nextState' = "precommit"
                        /\ UNCHANGED sectorStateError
             /\ pc' = [pc EXCEPT !["miner"] = "Reset"]
             /\ UNCHANGED << sectorState, wpostFlag, failedPoSts, skippedFault, 
                             penalties, epoch >>

Commit == /\ pc["miner"] = "Commit"
          /\ IF sectorState /= "precommit"
                THEN /\ sectorStateError' = "invalid commit"
                     /\ UNCHANGED nextState
                ELSE /\ nextState' = "active"
                     /\ UNCHANGED sectorStateError
          /\ pc' = [pc EXCEPT !["miner"] = "Reset"]
          /\ UNCHANGED << sectorState, wpostFlag, failedPoSts, skippedFault, 
                          penalties, epoch >>

DeclareFault == /\ pc["miner"] = "DeclareFault"
                /\ IF sectorState \in {"active", "faulty"}
                      THEN /\ wpostFlag' = "faulted"
                           /\ UNCHANGED sectorStateError
                      ELSE /\ sectorStateError' = "invalid declare fault"
                           /\ UNCHANGED wpostFlag
                /\ pc' = [pc EXCEPT !["miner"] = "Reset"]
                /\ UNCHANGED << sectorState, failedPoSts, skippedFault, 
                                nextState, penalties, epoch >>

DeclareRecovery == /\ pc["miner"] = "DeclareRecovery"
                   /\ IF sectorState = "faulty"
                         THEN /\ wpostFlag' = "recovered"
                              /\ UNCHANGED sectorStateError
                         ELSE /\ sectorStateError' = "invalid declare fault"
                              /\ UNCHANGED wpostFlag
                   /\ pc' = [pc EXCEPT !["miner"] = "Reset"]
                   /\ UNCHANGED << sectorState, failedPoSts, skippedFault, 
                                   nextState, penalties, epoch >>

WindowPoSt == /\ pc["miner"] = "WindowPoSt"
              /\ IF sectorState \in {"active", "faulty"}
                    THEN /\ IF sectorState = "active" /\ wpostFlag = NULLFLAG /\ skippedFault
                               THEN /\ nextState' = "faulty"
                               ELSE /\ IF sectorState = "active" /\ wpostFlag = "faulted"
                                          THEN /\ nextState' = "faulty"
                                          ELSE /\ IF sectorState = "faulty" /\ wpostFlag = "recovered" /\ ~skippedFault
                                                     THEN /\ nextState' = "active"
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED nextState
                         /\ IF (sectorState = "faulty" /\ nextState' = NULLSTATE) \/ nextState' = "faulty"
                               THEN /\ failedPoSts' = failedPoSts + 1
                               ELSE /\ failedPoSts' = 0
                         /\ IF failedPoSts' > 3
                               THEN /\ penalties' = TF
                               ELSE /\ IF sectorState = "faulty" /\ wpostFlag = "recovered" /\ skippedFault
                                          THEN /\ penalties' = SP
                                          ELSE /\ IF nextState' = "faulty"
                                                     THEN /\ penalties' = SP
                                                     ELSE /\ IF sectorState = "faulty" \/ (sectorState = "active" /\ wpostFlag = "faulted")
                                                                THEN /\ penalties' = FF
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED penalties
                    ELSE /\ TRUE
                         /\ UNCHANGED << failedPoSts, nextState, penalties >>
              /\ pc' = [pc EXCEPT !["miner"] = "WindowPoStReset"]
              /\ UNCHANGED << sectorState, wpostFlag, skippedFault, 
                              sectorStateError, epoch >>

WindowPoStReset == /\ pc["miner"] = "WindowPoStReset"
                   /\ wpostFlag' = NULLFLAG
                   /\ pc' = [pc EXCEPT !["miner"] = "Reset"]
                   /\ UNCHANGED << sectorState, failedPoSts, skippedFault, 
                                   nextState, penalties, sectorStateError, 
                                   epoch >>

Reset == /\ pc["miner"] = "Reset"
         /\ IF nextState /= NULLSTATE
               THEN /\ sectorState' = nextState
               ELSE /\ TRUE
                    /\ UNCHANGED sectorState
         /\ nextState' = NULLSTATE
         /\ penalties' = ZERO
         /\ sectorStateError' = NOERROR
         /\ \E x \in BOOLEAN:
              skippedFault' = x
         /\ pc' = [pc EXCEPT !["miner"] = "Blockchain"]
         /\ UNCHANGED << wpostFlag, failedPoSts, epoch >>

miner == Blockchain \/ Block \/ PreCommit \/ Commit \/ DeclareFault
            \/ DeclareRecovery \/ WindowPoSt \/ WindowPoStReset \/ Reset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == miner
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(miner)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-75eaae1e3673e421867e24fad1ae4eb1
====
