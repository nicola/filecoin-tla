---- MODULE faults ----
EXTENDS Integers, TLC

\* Faults
ZERO == "0"
FF == "ff"
SP == "sp"
TF == "tf"
PreCommitDeposit == "pcd"

\* Tooling
NOERROR == "no sectorStateError"
NULLSTATE == "null state"
NULLDECL == "null decl"
NULLMETHOD == "null method"

SectorStates == { "precommit", "active", "faulty", "clear" }
Declarations == { "faulted", "recovered" }
Methods == {"PreCommit", "Commit", "WindowPoSt", "DeclareFault", "DeclareRecovery"}

States == {
    \* Precommit
    [method |-> "PreCommit",    state |-> "clear",      stateNext |-> "precommit",  decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],

    \* Commit
    [method |-> "Commit",       state |-> "precommit",  stateNext |-> "active",     decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],

    \* WindowPoSt
    \* - honest
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],
    \* - continued faults
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> FF],
    \*     - with termination
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> "done",    decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> TF],
    \* - new declared faults
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> "faulty",     decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> FF],
    \* - skipped faults
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> "faulty",     decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> SP],
    \* - recovered
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> "active",     decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> ZERO],
    \* - failed recovery
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> SP],
    \*     - with termination
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> "done",    decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> TF],
    \* - recovered fault reported faulty again
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> FF],
    \*     - with termination
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> "done",    decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> TF],

    \* DeclareFaults
    \* - active is now faulted
    [method |-> "DeclareFault", state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "faulted",   penalties |-> ZERO],
    \* - recovered is now faulted
    [method |-> "DeclareFault", state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  "faulted",   penalties |-> ZERO],

    \* DeclareRecovery
    \* - faulty is now recovered
    [method |-> "DeclareRecovery", state |-> "faulty",  stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "recovered", penalties |-> ZERO]
}

Transitions == { <<x["method"], x["state"], x["stateNext"], x["decl"], x["declNext"]>> : x \in States }

(*--algorithm faults
variables
    sectorState \in SectorStates,
    sectorStateNext = NULLSTATE,
    sectorStateError = NOERROR,
    
    declaration = NULLDECL,
    declarationNext = NULLDECL,
    
    failedPoSts \in 1..2,
    skippedFault \in BOOLEAN,
    penalties = ZERO,
    
    methodCalled = NULLMETHOD;

define
    MessageExecuted == pc["miner"] = "End"
    NoErrors == sectorStateError = NOERROR
    PackState(method, state, stateNext, decl, declNext, pen) == [
        method |-> method,
        state |-> state,
        stateNext |-> stateNext,
        decl |-> decl,
        declNext |-> declNext,
        penalties |-> pen
    ]

    MessageInvariants == LET
        ValidMessage == <<methodCalled, sectorState, sectorStateNext, declaration, declarationNext>> \in Transitions
        ValidMessageNoError ==  ValidMessage /\ NoErrors
        InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
    IN MessageExecuted => ValidMessageNoError \/ InvalidMessageHaveError

    PenaltiesInvariants == LET
        ValidPenalty == PackState(methodCalled, sectorState, sectorStateNext, declaration, declarationNext, penalties) \in States
    IN MessageExecuted /\ NoErrors => ValidPenalty

    ExpectingProof == (sectorState = "active" /\ declaration = NULLDECL) \/ (sectorState = "faulty" /\ declaration = "recovered")
    SkippedFault == ExpectingProof /\ skippedFault
    FailedRecoveryDeclaredFault == sectorState = "faulty" \/ declaration = "faulted"
    ContinuedDeclaredFault == sectorState = "faulty" /\ declaration = NULLDECL
    NewDeclaredFault == sectorState = "active" /\ declaration = "faulted"
    DeclaredFault == FailedRecoveryDeclaredFault \/ ContinuedDeclaredFault \/ NewDeclaredFault
    RecoveredFault == sectorState = "faulty" /\ declaration = "recovered" /\ ~skippedFault

end define;

fair+ process miner = "miner"
variables epoch = 0
begin
    Blockchain:
        while epoch < 5 do
            epoch := epoch + 1;
            Block:
                either
                    PreCommit:
                        methodCalled := "PreCommit";
                        if sectorState /= "clear" then
                            sectorStateError := "invalid precommit";
                        else
                            \* Mark sector as committed
                            sectorStateNext := "precommit";
                        end if;
                or
                    Commit:
                        methodCalled := "Commit";
                        if sectorState /= "precommit" then
                            sectorStateError := "invalid commit";
                        else
                            \* Mark sector as active
                            sectorStateNext := "active";
                        end if;   
                or
                    DeclareFault:
                        methodCalled := "DeclareFault";
                        \* Declare active sector as faulted
                        if sectorState = "active" /\ declaration /= NULLDECL then
                            declarationNext := "faulted";
                        \* Declare recovered faulty sector as faulted
                        elsif sectorState = "faulty" /\ declaration = "recovered" then
                            declarationNext := "faulted";                            
                        else
                            sectorStateError := "invalid declare fault";
                        end if;
                or
                    DeclareRecovery:
                        methodCalled := "DeclareRecovery";
                        if sectorState = "faulty" /\ declaration = NULLDECL then
                            declarationNext := "recovered";
                        else
                            sectorStateError := "invalid declare recovery";
                        end if;
                or
                    WindowPoSt:
                        methodCalled := "WindowPoSt";
                        if sectorState \in {"active", "faulty"} then

                            \* - skipped faults
                            \* - failed recovery
                            if RecoveredFault then
                                sectorStateNext := "active";
                            elsif SkippedFault then
                                if sectorState = "active" then
                                    sectorStateNext := "faulty";
                                end if;
                                penalties := SP;

                            \* - continued faults
                            \* - recovered fault reported faulty again
                            \* - new declared faults
                            elsif DeclaredFault then
                                if sectorState = "active" then
                                    sectorStateNext := "faulty";
                                end if;
                                penalties := FF;
                            \* - recovered
                            end if;

                            \* Update faults counter when the sector is faulty
                            \* either the sector is faulty already
                            \*     or the sector is found to be faulty
                            if sectorStateNext /= "active" /\ (DeclareFault \/ SkippedFault) then
                                failedPoSts := failedPoSts + 1;
                            else
                                failedPoSts := 0;
                            end if;

                            \* Apply penalties
                            ApplyPenalty:
                                if failedPoSts > 3 then
                                    penalties := TF;
                                    sectorStateNext := "done";
                                end if;
                        else
                            sectorStateError := "sector was not active nor faulty";
                        end if;
                        \* Termination

                end either;
                End:
                    if sectorStateNext /= NULLSTATE then
                        sectorState := sectorStateNext;
                    end if;

                    if methodCalled = "WindowPoSt" then
                        declaration := NULLDECL;
                    else
                        declaration := declarationNext;
                    end if;
                    methodCalled := NULLMETHOD;
                    declarationNext := NULLDECL;
                    sectorStateNext := NULLSTATE;
                    penalties := ZERO;
                    sectorStateError := NOERROR;
                    with x \in BOOLEAN  do
                        skippedFault := x;
                    end with; 
                    
                    
        end while;
end process;

end algorithm; *)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f314d3c8662aa26f62b7d61fda6ee8f2
VARIABLES sectorState, sectorStateNext, sectorStateError, declaration, 
          declarationNext, failedPoSts, skippedFault, penalties, methodCalled, 
          pc

(* define statement *)
MessageExecuted == pc["miner"] = "End"
NoErrors == sectorStateError = NOERROR
PackState(method, state, stateNext, decl, declNext, pen) == [
    method |-> method,
    state |-> state,
    stateNext |-> stateNext,
    decl |-> decl,
    declNext |-> declNext,
    penalties |-> pen
]

MessageInvariants == LET
    ValidMessage == <<methodCalled, sectorState, sectorStateNext, declaration, declarationNext>> \in Transitions
    ValidMessageNoError ==  ValidMessage /\ NoErrors
    InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
IN MessageExecuted => ValidMessageNoError \/ InvalidMessageHaveError

PenaltiesInvariants == LET
    ValidPenalty == PackState(methodCalled, sectorState, sectorStateNext, declaration, declarationNext, penalties) \in States
IN MessageExecuted /\ NoErrors => ValidPenalty

ExpectingProof == (sectorState = "active" /\ declaration = NULLDECL) \/ (sectorState = "faulty" /\ declaration = "recovered")
SkippedFault == ExpectingProof /\ skippedFault
FailedRecoveryDeclaredFault == sectorState = "faulty" \/ declaration = "faulted"
ContinuedDeclaredFault == sectorState = "faulty" /\ declaration = NULLDECL
NewDeclaredFault == sectorState = "active" /\ declaration = "faulted"
DeclaredFault == FailedRecoveryDeclaredFault \/ ContinuedDeclaredFault \/ NewDeclaredFault
RecoveredFault == sectorState = "faulty" /\ declaration = "recovered" /\ ~skippedFault

VARIABLE epoch

vars == << sectorState, sectorStateNext, sectorStateError, declaration, 
           declarationNext, failedPoSts, skippedFault, penalties, 
           methodCalled, pc, epoch >>

ProcSet == {"miner"}

Init == (* Global variables *)
        /\ sectorState \in SectorStates
        /\ sectorStateNext = NULLSTATE
        /\ sectorStateError = NOERROR
        /\ declaration = NULLDECL
        /\ declarationNext = NULLDECL
        /\ failedPoSts \in 1..2
        /\ skippedFault \in BOOLEAN
        /\ penalties = ZERO
        /\ methodCalled = NULLMETHOD
        (* Process miner *)
        /\ epoch = 0
        /\ pc = [self \in ProcSet |-> "Blockchain"]

Blockchain == /\ pc["miner"] = "Blockchain"
              /\ IF epoch < 5
                    THEN /\ epoch' = epoch + 1
                         /\ pc' = [pc EXCEPT !["miner"] = "Block"]
                    ELSE /\ pc' = [pc EXCEPT !["miner"] = "Done"]
                         /\ epoch' = epoch
              /\ UNCHANGED << sectorState, sectorStateNext, sectorStateError, 
                              declaration, declarationNext, failedPoSts, 
                              skippedFault, penalties, methodCalled >>

Block == /\ pc["miner"] = "Block"
         /\ \/ /\ pc' = [pc EXCEPT !["miner"] = "PreCommit"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "Commit"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "DeclareFault"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "DeclareRecovery"]
            \/ /\ pc' = [pc EXCEPT !["miner"] = "WindowPoSt"]
         /\ UNCHANGED << sectorState, sectorStateNext, sectorStateError, 
                         declaration, declarationNext, failedPoSts, 
                         skippedFault, penalties, methodCalled, epoch >>

PreCommit == /\ pc["miner"] = "PreCommit"
             /\ methodCalled' = "PreCommit"
             /\ IF sectorState /= "clear"
                   THEN /\ sectorStateError' = "invalid precommit"
                        /\ UNCHANGED sectorStateNext
                   ELSE /\ sectorStateNext' = "precommit"
                        /\ UNCHANGED sectorStateError
             /\ pc' = [pc EXCEPT !["miner"] = "End"]
             /\ UNCHANGED << sectorState, declaration, declarationNext, 
                             failedPoSts, skippedFault, penalties, epoch >>

Commit == /\ pc["miner"] = "Commit"
          /\ methodCalled' = "Commit"
          /\ IF sectorState /= "precommit"
                THEN /\ sectorStateError' = "invalid commit"
                     /\ UNCHANGED sectorStateNext
                ELSE /\ sectorStateNext' = "active"
                     /\ UNCHANGED sectorStateError
          /\ pc' = [pc EXCEPT !["miner"] = "End"]
          /\ UNCHANGED << sectorState, declaration, declarationNext, 
                          failedPoSts, skippedFault, penalties, epoch >>

DeclareFault == /\ pc["miner"] = "DeclareFault"
                /\ methodCalled' = "DeclareFault"
                /\ IF sectorState = "active" /\ declaration /= NULLDECL
                      THEN /\ declarationNext' = "faulted"
                           /\ UNCHANGED sectorStateError
                      ELSE /\ IF sectorState = "faulty" /\ declaration = "recovered"
                                 THEN /\ declarationNext' = "faulted"
                                      /\ UNCHANGED sectorStateError
                                 ELSE /\ sectorStateError' = "invalid declare fault"
                                      /\ UNCHANGED declarationNext
                /\ pc' = [pc EXCEPT !["miner"] = "End"]
                /\ UNCHANGED << sectorState, sectorStateNext, declaration, 
                                failedPoSts, skippedFault, penalties, epoch >>

DeclareRecovery == /\ pc["miner"] = "DeclareRecovery"
                   /\ methodCalled' = "DeclareRecovery"
                   /\ IF sectorState = "faulty" /\ declaration = NULLDECL
                         THEN /\ declarationNext' = "recovered"
                              /\ UNCHANGED sectorStateError
                         ELSE /\ sectorStateError' = "invalid declare recovery"
                              /\ UNCHANGED declarationNext
                   /\ pc' = [pc EXCEPT !["miner"] = "End"]
                   /\ UNCHANGED << sectorState, sectorStateNext, declaration, 
                                   failedPoSts, skippedFault, penalties, epoch >>

WindowPoSt == /\ pc["miner"] = "WindowPoSt"
              /\ methodCalled' = "WindowPoSt"
              /\ IF sectorState \in {"active", "faulty"}
                    THEN /\ IF RecoveredFault
                               THEN /\ sectorStateNext' = "active"
                                    /\ UNCHANGED penalties
                               ELSE /\ IF SkippedFault
                                          THEN /\ IF sectorState = "active"
                                                     THEN /\ sectorStateNext' = "faulty"
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED sectorStateNext
                                               /\ penalties' = SP
                                          ELSE /\ IF DeclaredFault
                                                     THEN /\ IF sectorState = "active"
                                                                THEN /\ sectorStateNext' = "faulty"
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED sectorStateNext
                                                          /\ penalties' = FF
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED << sectorStateNext, 
                                                                          penalties >>
                         /\ IF sectorStateNext' /= "active" /\ (DeclareFault \/ SkippedFault)
                               THEN /\ failedPoSts' = failedPoSts + 1
                               ELSE /\ failedPoSts' = 0
                         /\ pc' = [pc EXCEPT !["miner"] = "ApplyPenalty"]
                         /\ UNCHANGED sectorStateError
                    ELSE /\ sectorStateError' = "sector was not active nor faulty"
                         /\ pc' = [pc EXCEPT !["miner"] = "End"]
                         /\ UNCHANGED << sectorStateNext, failedPoSts, 
                                         penalties >>
              /\ UNCHANGED << sectorState, declaration, declarationNext, 
                              skippedFault, epoch >>

ApplyPenalty == /\ pc["miner"] = "ApplyPenalty"
                /\ IF failedPoSts > 3
                      THEN /\ penalties' = TF
                           /\ sectorStateNext' = "done"
                      ELSE /\ TRUE
                           /\ UNCHANGED << sectorStateNext, penalties >>
                /\ pc' = [pc EXCEPT !["miner"] = "End"]
                /\ UNCHANGED << sectorState, sectorStateError, declaration, 
                                declarationNext, failedPoSts, skippedFault, 
                                methodCalled, epoch >>

End == /\ pc["miner"] = "End"
       /\ IF sectorStateNext /= NULLSTATE
             THEN /\ sectorState' = sectorStateNext
             ELSE /\ TRUE
                  /\ UNCHANGED sectorState
       /\ IF methodCalled = "WindowPoSt"
             THEN /\ declaration' = NULLDECL
             ELSE /\ declaration' = declarationNext
       /\ methodCalled' = NULLMETHOD
       /\ declarationNext' = NULLDECL
       /\ sectorStateNext' = NULLSTATE
       /\ penalties' = ZERO
       /\ sectorStateError' = NOERROR
       /\ \E x \in BOOLEAN:
            skippedFault' = x
       /\ pc' = [pc EXCEPT !["miner"] = "Blockchain"]
       /\ UNCHANGED << failedPoSts, epoch >>

miner == Blockchain \/ Block \/ PreCommit \/ Commit \/ DeclareFault
            \/ DeclareRecovery \/ WindowPoSt \/ ApplyPenalty \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == miner
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(miner)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a52d62fa38c46a6e542f85a723df7f24
====
