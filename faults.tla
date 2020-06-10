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

\* `Transition` - All valid transitions for the storage Miner
\* - `method`: the Actor method called 
\* - `state`: the sector state at the beginning of the call
\* - `stateNext`: the sector state at the end of the call
\* - `decl`: the state of the declaration of a sector at the beginning of the call
\* - `declNext`: the state of the declaration at the end of the call
\* - `penalties`: the penalty paid by the end of the call
Transitions == {
    \* Precommit: A clear sector is precommitted (clear ->  precommit)
    [method |-> "PreCommit",       state |-> "clear",      stateNext |-> "precommit",  decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],

    \* Commit: A precommitted sector becomes active (precommit -> active)
    [method |-> "Commit",          state |-> "precommit",  stateNext |-> "active",     decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],

    \* WindowPoSt
    \* - honest: An active sector remains active
    [method |-> "WindowPoSt",      state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> ZERO],
    \* - continued faults: A faulty sector remains faulty
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> FF],
    \*     - with termination: if faulty for too long, it's terminated
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> "done",       decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> TF],
    \* - new declared faults: An active sector that is declared faulted becomes faulty
    [method |-> "WindowPoSt",      state |-> "active",     stateNext |-> "faulty",     decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> FF],
    \* - skipped faults: An active sector not declared faulty that fails post becomes faulty
    [method |-> "WindowPoSt",      state |-> "active",     stateNext |-> "faulty",     decl |-> NULLDECL,    declNext |->  NULLDECL,    penalties |-> SP],
    \* - recovered: An faulty sector that is declared recovered becomes active
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> "active",     decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> ZERO],
    \* - failed recovery: A faulty sector that is claimed recovered but fails post is penalized as skipped fault 
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> SP],
    \*     - with termination: if faulty for too long, it's terminated
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> "done",       decl |-> "recovered", declNext |->  NULLDECL,    penalties |-> TF],
    \* - recovered fault reported faulty again: A faulty sector is declared faulted (from a previous recovery)
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> FF],
    \*     - with termination: if faulty for too long, it's terminated
    [method |-> "WindowPoSt",      state |-> "faulty",     stateNext |-> "done",       decl |-> "faulted",   declNext |->  NULLDECL,    penalties |-> TF],

    \* DeclareFaults
    \* - active is now faulted: An active sector is declared as faulted
    [method |-> "DeclareFault",    state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "faulted",   penalties |-> ZERO],
    \* - recovered is now faulted: A faulty sector is declared faulted again (from a previous recovery)
    [method |-> "DeclareFault",    state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  "faulted",   penalties |-> ZERO],

    \* DeclareRecovery
    \* - faulty is now recovered: A faulty sector is declared recovered
    [method |-> "DeclareRecovery", state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "recovered", penalties |-> ZERO]
}

\* StateTransitions - Same as Transitions without penalties
StateTransitions == { <<x["method"], x["state"], x["stateNext"], x["decl"], x["declNext"]>> : x \in Transitions }

(*--algorithm faults
variables
    \* sector state before a method call
    sectorState \in SectorStates,
    \* sector state at the end of a method call
    sectorStateNext = NULLSTATE,
    \* error from an invalid sector state transition
    sectorStateError = NOERROR,
    
    \* declaration before a method call
    declaration = NULLDECL,
    \* declaration after a method call
    declarationNext = NULLDECL,
    
    \* consecutive posts failed so far
    failedPoSts \in 0..2,
    \* decide whether a fault is being skipped or not
    skippedFault \in BOOLEAN,
    \* penalties to be paid by the end of the method call
    penalties = ZERO,
    
    \* last method called
    methodCalled = NULLMETHOD;

define
    \* MessageExecuted - True when we reach end of method call
    MessageExecuted == pc["miner"] = "End"

    \* NoErrors - True when no error
    NoErrors == sectorStateError = NOERROR

    \* PackTransition - Utility to pack variables into a struct
    PackTransition(method, state, stateNext, decl, declNext, pen) == [
        method |-> method,
        state |-> state,
        stateNext |-> stateNext,
        decl |-> decl,
        declNext |-> declNext,
        penalties |-> pen
    ]

    \* INVARIANTS

    \* MessageInvariants - All messages are valid or faults are reported
    MessageInvariants == LET
        ValidMessage == <<methodCalled, sectorState, sectorStateNext, declaration, declarationNext>> \in StateTransitions
        ValidMessageNoError ==  ValidMessage /\ NoErrors
        InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
    IN MessageExecuted => ValidMessageNoError \/ InvalidMessageHaveError

    \* PenaltyInvariants - If there are no errors, penalties must be set correctly
    PenaltiesInvariants == LET
        ValidPenalty == PackTransition(methodCalled, sectorState, sectorStateNext, declaration, declarationNext, penalties) \in Transitions
    IN MessageExecuted /\ NoErrors => ValidPenalty

    \* Faults utility

    \* ExpectingProof - WindowPoSt expects a sector proof
    ExpectingProof == (sectorState = "active" /\ declaration = NULLDECL) \/ (sectorState = "faulty" /\ declaration = "recovered")
    \* SkippedFault - WindowPoSt expected a proof that did not appear/faulty
    SkippedFault == ExpectingProof /\ skippedFault
    \* FailedRecoveryDeclaredFault - A faulty sector is still declared faulty (after being recovered)
    FailedRecoveryDeclaredFault == sectorState = "faulty" /\ declaration = "faulted"
    \* ContinuedDeclaredFault - A sector is faulty and continues being so
    ContinuedDeclaredFault == sectorState = "faulty" /\ declaration = NULLDECL
    \* NewDeclaredFault - A sector is active and declared as faulty
    NewDeclaredFault == sectorState = "active" /\ declaration = "faulted"
    \* DeclaredFault - A sector is declared as faulty
    DeclaredFault == FailedRecoveryDeclaredFault \/ ContinuedDeclaredFault \/ NewDeclaredFault
    \* RecoveredFault - A sector is recovered
    RecoveredFault == sectorState = "faulty" /\ declaration = "recovered" /\ ~skippedFault

end define;

fair+ process miner = "miner"
variables epoch = 0
begin
    \* Blockchain - This is the blockchain utility and runs multiple epochs
    \* At each epoch, we execute a block and in each block we execute one
    \* method call
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

                \* Reset to initial conditions
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


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-143c3bd8938b9634ebb7962318db2193
VARIABLES sectorState, sectorStateNext, sectorStateError, declaration, 
          declarationNext, failedPoSts, skippedFault, penalties, methodCalled, 
          pc

(* define statement *)
MessageExecuted == pc["miner"] = "End"


NoErrors == sectorStateError = NOERROR


PackTransition(method, state, stateNext, decl, declNext, pen) == [
    method |-> method,
    state |-> state,
    stateNext |-> stateNext,
    decl |-> decl,
    declNext |-> declNext,
    penalties |-> pen
]




MessageInvariants == LET
    ValidMessage == <<methodCalled, sectorState, sectorStateNext, declaration, declarationNext>> \in StateTransitions
    ValidMessageNoError ==  ValidMessage /\ NoErrors
    InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
IN MessageExecuted => ValidMessageNoError \/ InvalidMessageHaveError


PenaltiesInvariants == LET
    ValidPenalty == PackTransition(methodCalled, sectorState, sectorStateNext, declaration, declarationNext, penalties) \in Transitions
IN MessageExecuted /\ NoErrors => ValidPenalty




ExpectingProof == (sectorState = "active" /\ declaration = NULLDECL) \/ (sectorState = "faulty" /\ declaration = "recovered")

SkippedFault == ExpectingProof /\ skippedFault

FailedRecoveryDeclaredFault == sectorState = "faulty" /\ declaration = "faulted"

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
        /\ failedPoSts \in 0..2
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-fb7983c311362fab4f28c039a599a8e1
====
