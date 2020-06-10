---- MODULE faults ----
EXTENDS Integers, TLC

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

NULLDECL == "null decl"
NULLMETHOD == "null method"

SectorStates == { "precommit", "active", "faulty", "null" }
SectorStateTs == {
    \* Honest transitions
    <<"null", "precommit", {ZERO}>>,
    <<"precommit", "active", {ZERO}>>,

    \* Faults
    <<"active", "faulty", {FF, SP}>>,
    <<"faulty", "active", {ZERO}>>

    \* sectors are terminated
    \* <<"faulty", "done", {FF, SP, TF}>>,
    \* <<"active", "done", {ZERO, TF}>>,

    \* Sector is cleaned up, ID can be reused
    \* <<"precommit", "null", {PreCommitDeposit}>>
}

Methods == {"PreCommit", "Commit", "WindowPoSt", "DeclareFault", "DeclareRecovery"}
SectorStateMessages == {
    \* Precommit
    [method |-> "PreCommit",    state |-> "null",       stateNext |-> "precommit",  decl |-> NULLDECL,    declNext |->  NULLDECL],

    \* Commit
    [method |-> "Commit",       state |-> "precommit",  stateNext |-> "active",     decl |-> NULLDECL,    declNext |->  NULLDECL],

    \* WindowPoSt
    \* - honest
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL],
    \* - continued faults
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  NULLDECL],
    \* - new declared faults
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> "faulty",     decl |-> "faulted",   declNext |->  NULLDECL],
    \* - skipped faults
    [method |-> "WindowPoSt",   state |-> "active",     stateNext |-> "faulty",     decl |-> NULLDECL,    declNext |->  NULLDECL],
    \* - recovered
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> "active",     decl |-> "recovered", declNext |->  NULLDECL],
    \* - failed recovery
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  NULLDECL],
    \* - recovered fault reported faulty again
    [method |-> "WindowPoSt",   state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "faulted",   declNext |->  NULLDECL],

    \* DeclareFaults
    \* - active is now faulted
    [method |-> "DeclareFault", state |-> "active",     stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "faulted"],
    \* - recovered is now faulted
    [method |-> "DeclareFault", state |-> "faulty",     stateNext |-> NULLSTATE,    decl |-> "recovered", declNext |->  "faulted"],

    \* DeclareRecovery
    \* - faulty is now recovered
    [method |-> "DeclareRecovery", state |-> "faulty",  stateNext |-> NULLSTATE,    decl |-> NULLDECL,    declNext |->  "recovered"]
}

Declarations == { "recovered", "faulted" }
DeclarationTs == {
    <<"active", "faulted", "faulty">>,
    <<"faulty", "recovered", "active">>,
    <<"faulty", "faulted", NULLSTATE>>
}

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
    InitTs == LET
        SectorStateInit == sectorStateNext = NULLSTATE /\ sectorStateError = NOERROR
        DeclarationInit == declaration = NULLDECL
    IN SectorStateInit /\ DeclarationInit

    SectorStateTransition(from, to) == <<from, to>> \in { <<x[1], x[2]>> : x \in SectorStateTs }
    ValidDeclaration(from, flag) == <<from, flag>> \in { <<x[1], x[2]>> : x \in DeclarationTs }
    ValidDeclarationTs(from, flag, to) == <<from, flag, to>> \in DeclarationTs
    PackState(method, state, stateNext, decl, declNext) == [ method |-> method, state |-> state, stateNext |-> stateNext, decl |-> decl, declNext |-> declNext]

    NoErrors == sectorStateError = NOERROR

    PackedState == PackState(methodCalled, sectorState, sectorStateNext, declaration, declarationNext)
    ValidMessage == PackedState \in SectorStateMessages
    ValidMessageNoError ==  ValidMessage /\ NoErrors
    InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
    MessageInvariants == pc["miner"] = "End" => ValidMessageNoError \/ InvalidMessageHaveError

    SectorStateInvariants == LET
        \* A valid state transition has no sectorStateError
        ValidStateTs == sectorStateNext /= NULLSTATE => (SectorStateTransition(sectorState, sectorStateNext) /\ sectorStateError = NOERROR)
        \* An invalid state transition has an sectorStateError
        InvalidStateTsHaveError == ~SectorStateTransition(sectorState, sectorStateNext) /\ sectorStateError /= NOERROR
        \* Initial state
    IN  ValidStateTs \/ InvalidStateTsHaveError \/ InitTs

    DeclarationInvariants == LET 
        DeclaredState == sectorState \in {"active", "faulty"} /\ declaration /= NULLDECL
        ValidDeclarationState ==  DeclaredState /\ sectorStateNext = NULLSTATE => ValidDeclaration(sectorState, declaration)
        ValidDeclarationExecution == DeclaredState /\ sectorStateNext /= NULLSTATE => ValidDeclarationTs(sectorState, declaration, sectorStateNext)
    IN (ValidDeclarationState /\ ValidDeclarationExecution) \/ InitTs

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
                        methodCalled := "PreCommit";
                        if sectorState /= "null" then
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
                            \* State changes
                            \* Active -> Faulty: SkippedFault
                            if sectorState = "active" /\ declaration = NULLDECL /\ skippedFault then
                                sectorStateNext := "faulty";
                            \* Active -> Faulty: DeclareFault
                            elsif sectorState = "active" /\ declaration = "faulted" then
                                sectorStateNext := "faulty";
                            \* Faulty -> Active: DeclareRecovery
                            elsif sectorState = "faulty" /\ declaration = "recovered" /\ ~skippedFault then
                                sectorStateNext := "active";
                            end if;
                            
                            \* Update faults counter when the sector is faulty
                            \* either the sector is faulty already
                            \*     or the sector is found to be faulty
                            if (sectorState = "faulty" /\ sectorStateNext = NULLSTATE) \/ sectorStateNext = "faulty" then
                                failedPoSts := failedPoSts + 1;
                            else
                                failedPoSts := 0;
                            end if;

                            \* Apply penalties
                            if failedPoSts > 3 then
                                penalties := TF;
                            elsif sectorState = "faulty" /\ declaration = "recovered" /\ skippedFault then
                                penalties := SP;
                            elsif sectorStateNext = "faulty" then
                                penalties := SP;
                            elsif sectorState = "faulty" \/ (sectorState = "active" /\ declaration = "faulted") then
                                penalties := FF;
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


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b51d1d0e03ee0a3a165016c599b5bd00
VARIABLES sectorState, sectorStateNext, sectorStateError, declaration, 
          declarationNext, failedPoSts, skippedFault, penalties, methodCalled, 
          pc

(* define statement *)
InitTs == LET
    SectorStateInit == sectorStateNext = NULLSTATE /\ sectorStateError = NOERROR
    DeclarationInit == declaration = NULLDECL
IN SectorStateInit /\ DeclarationInit

SectorStateTransition(from, to) == <<from, to>> \in { <<x[1], x[2]>> : x \in SectorStateTs }
ValidDeclaration(from, flag) == <<from, flag>> \in { <<x[1], x[2]>> : x \in DeclarationTs }
ValidDeclarationTs(from, flag, to) == <<from, flag, to>> \in DeclarationTs
PackState(method, state, stateNext, decl, declNext) == [ method |-> method, state |-> state, stateNext |-> stateNext, decl |-> decl, declNext |-> declNext]

NoErrors == sectorStateError = NOERROR

PackedState == PackState(methodCalled, sectorState, sectorStateNext, declaration, declarationNext)
ValidMessage == PackedState \in SectorStateMessages
ValidMessageNoError ==  ValidMessage /\ NoErrors
InvalidMessageHaveError == ~ValidMessage /\ ~NoErrors
MessageInvariants == pc["miner"] = "End" => ValidMessageNoError \/ InvalidMessageHaveError

SectorStateInvariants == LET

    ValidStateTs == sectorStateNext /= NULLSTATE => (SectorStateTransition(sectorState, sectorStateNext) /\ sectorStateError = NOERROR)

    InvalidStateTsHaveError == ~SectorStateTransition(sectorState, sectorStateNext) /\ sectorStateError /= NOERROR

IN  ValidStateTs \/ InvalidStateTsHaveError \/ InitTs

DeclarationInvariants == LET
    DeclaredState == sectorState \in {"active", "faulty"} /\ declaration /= NULLDECL
    ValidDeclarationState ==  DeclaredState /\ sectorStateNext = NULLSTATE => ValidDeclaration(sectorState, declaration)
    ValidDeclarationExecution == DeclaredState /\ sectorStateNext /= NULLSTATE => ValidDeclarationTs(sectorState, declaration, sectorStateNext)
IN (ValidDeclarationState /\ ValidDeclarationExecution) \/ InitTs

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
              /\ IF epoch < 3
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
             /\ IF sectorState /= "null"
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
                    THEN /\ IF sectorState = "active" /\ declaration = NULLDECL /\ skippedFault
                               THEN /\ sectorStateNext' = "faulty"
                               ELSE /\ IF sectorState = "active" /\ declaration = "faulted"
                                          THEN /\ sectorStateNext' = "faulty"
                                          ELSE /\ IF sectorState = "faulty" /\ declaration = "recovered" /\ ~skippedFault
                                                     THEN /\ sectorStateNext' = "active"
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED sectorStateNext
                         /\ IF (sectorState = "faulty" /\ sectorStateNext' = NULLSTATE) \/ sectorStateNext' = "faulty"
                               THEN /\ failedPoSts' = failedPoSts + 1
                               ELSE /\ failedPoSts' = 0
                         /\ IF failedPoSts' > 3
                               THEN /\ penalties' = TF
                               ELSE /\ IF sectorState = "faulty" /\ declaration = "recovered" /\ skippedFault
                                          THEN /\ penalties' = SP
                                          ELSE /\ IF sectorStateNext' = "faulty"
                                                     THEN /\ penalties' = SP
                                                     ELSE /\ IF sectorState = "faulty" \/ (sectorState = "active" /\ declaration = "faulted")
                                                                THEN /\ penalties' = FF
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED penalties
                         /\ UNCHANGED sectorStateError
                    ELSE /\ sectorStateError' = "sector was not active nor faulty"
                         /\ UNCHANGED << sectorStateNext, failedPoSts, 
                                         penalties >>
              /\ pc' = [pc EXCEPT !["miner"] = "End"]
              /\ UNCHANGED << sectorState, declaration, declarationNext, 
                              skippedFault, epoch >>

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
            \/ DeclareRecovery \/ WindowPoSt \/ End

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == miner
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(miner)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c889fe459ef6bb4f0a8a539509b7f5ac
====
