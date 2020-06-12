--------------------------- MODULE storageminer -----------------------------

EXTENDS Integers, TLC, FiniteSets
CONSTANTS precommit, active, faulty, clear, done, faulted, recovered
CONSTANTS FF, SP, TF, ZERO, PreCommitDeposit
CONSTANTS  NOERROR, NULLSTATE, NULLDECL, NULLMETHOD
CONSTANTS RegisteredProofs

T(method, state, stateNext, decl, declNext, pen) ==
  (*************************************************************************)
  (* Utility that packs a list into a struct.                              *)
  (*************************************************************************)
  [
    method |-> method,
    state |-> state,
    stateNext |-> stateNext,
    decl |-> decl,
    declNext |-> declNext,
    penalties |-> pen
  ]

(***************************************************************************)
(* StorageMiner Actor                                                      *)
(***************************************************************************)

Methods ==
  (*************************************************************************)
  (* The set of StorageMiner actor methods                                 *)
  (*************************************************************************)
  {
    "PreCommit",
    "Commit",
    "WindowPoSt",
    "DeclareFault",
    "DeclareRecovery",
    "TerminateSector"
  }

SectorStates == { precommit, active, faulty, clear }
  (*************************************************************************)
  (* The set of all sector states.                                         *)
  (*************************************************************************)

Declarations == { faulted, recovered }
  (*************************************************************************)
  (* The set of all declarations that are considered during WindowPoSt     *)
  (*************************************************************************)

Transitions ==
  (*************************************************************************)
  (* The set of all valid StorageMiner state transitions.                  *)
  (* - `method`: the Actor method called                                   *)
  (* - `state`: the sector state at the beginning of the call              *)
  (* - `stateNext`: the sector state at the end of the call                *)
  (* - `decl`: the state of the declaration of a sector at the beginning   *)
  (*    of the call                                                        *)
  (* - `declNext`: the state of the declaration at the end of the call     *)
  (* - `penalties`: the penalty paid by the end of the call                *)
  (*************************************************************************)
  {
    (***********************************************************************)
    (* Precommit: A clear sector is precommitted (clear ->  precommit).    *)
    (***********************************************************************)
    T("PreCommit", clear, precommit, NULLDECL, NULLDECL, ZERO),

    (***********************************************************************)
    (* Commit: A precommitted sector becomes active (precommit -> active). *)
    (***********************************************************************)
    T("Commit", precommit, active, NULLDECL, NULLDECL, ZERO),

    (***********************************************************************)
    (* WindowPoSt: Honest case                                             *)
    (* An active sector remains active.                                    *)
    (***********************************************************************)
    T("WindowPoSt", active, NULLSTATE, NULLDECL, NULLDECL, ZERO),
    
    (***********************************************************************)
    (* WindowPoSt: Continued Fault                                         *)
    (* A faulty sector remains faulty in absence of declarations.          *)
    (***********************************************************************)
    T("WindowPoSt", faulty, NULLSTATE, NULLDECL, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: New Declared Fault                                      *)
    (* An active sector that is declared faulted becomes faulty.           *)
    (***********************************************************************)
    T("WindowPoSt", active, faulty, faulted, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: Failed Recovery Declared Fault                          *)
    (* A faulty sector declared as recovered and then declared again as    *)
    (* faulted becomes faulty                                              *)
    (***********************************************************************)
    T("WindowPoSt", faulty, NULLSTATE, faulted, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: Active Skipped Faults                                   *)
    (* An active sector that is not declared faulted becomes faulty.       *)
    (***********************************************************************)
    T("WindowPoSt", active, faulty, NULLDECL, NULLDECL, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Skipped Fault                                 *)
    (* A faulty sector is declared recovered and then fails the proof      *)
    (* becomes faulty.                                                     *)
    (***********************************************************************)
    T("WindowPoSt", faulty, NULLSTATE, recovered, NULLDECL, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Sector                                        *)
    (* A faulty sector declared as recovered becomes active.               *)
    (***********************************************************************)
    T("WindowPoSt", faulty, active, recovered, NULLDECL, ZERO),

    (***********************************************************************)
    (* DeclareFault: New Declared Fault                                    *)
    (* An active sector is declared faulted.                               *)
    (***********************************************************************)
    T("DeclareFault", active, NULLSTATE, NULLDECL, faulted, ZERO),

    (***********************************************************************)
    (* DeclareFault: Failed Recovery Declared Fault                        *)
    (* A faulty sector that is declared as recovered is now redeclared as  *)
    (* faulty.                                                             *)
    (***********************************************************************)
    T("DeclareFault", faulty, NULLSTATE, recovered, faulted, ZERO),

    (***********************************************************************)
    (* DeclareRecovery: A faulty sector is marked as recovered.            *)
    (***********************************************************************)
    T("DeclareRecovery", faulty, NULLSTATE, NULLDECL, recovered, ZERO)
  }
  \union
  (*************************************************************************)
  (* TerminateSector: An active or faulty sector is terminated             *)
  (*************************************************************************)
  [
    method: {"TerminateSector"},
    state: {faulty, active},
    stateNext: {done},
    decl: {faulted, recovered, NULLDECL},
    declNext: {NULLDECL},
    penalties: {TF}
  ]
  \union 
  (*************************************************************************)
  (* WindowPoSt: Termination Faults                                        *)
  (* Continued Fault (Termination Fault version)                           *)
  (* Recovered Skipped Fault (Termination Fault version)                   *)
  (* Failed Recovery Declared Fault (Termination fault)                    *)
  (*************************************************************************)
  [
    method: {"WindowPoSt"},
    state: {faulty},
    stateNext: {done},
    decl: {NULLDECL, recovered, faulted},
    declNext: {NULLDECL},
    penalties: {TF}
  ]
      
(***************************************************************************)
(* Faults                                                                  *)
(***************************************************************************)

SkippedFault(state, decl, missedPoSt) == 
  (*************************************************************************)
  (* A SkippedFault occurs when an active sector or a recovered sector     *)
  (* fails to be proven at WindowPoSt                                      *)
  (*************************************************************************)
  LET 
    ActiveSector == (state = active /\ decl = NULLDECL)
    RecoverSector == (state = faulty /\ decl = recovered)
    ExpectingProof == ActiveSector \/ RecoverSector
  IN ExpectingProof /\ missedPoSt

DeclaredFault(state, decl) == 
  (*************************************************************************)
  (* A DeclaredFault occurs when a sector is known to be faulty.           *)
  (*************************************************************************)
  LET 
    FailedRecoveryDeclaredFault ==
      (*********************************************************************)
      (* A faulty sector is still declared faulty, after being recovered.  *)
      (*********************************************************************)
      state = faulty /\ decl = faulted

    ContinuedDeclaredFault ==
      (*********************************************************************)
      (* A sector is faulty and continues being so.                        *)
      (*********************************************************************)
      state = faulty /\ decl = NULLDECL

    NewDeclaredFault ==
      (*********************************************************************)
      (* A sector is active and declared as faulty.                        *)
      (*********************************************************************)
      state = active /\ decl = faulted

  IN \/ FailedRecoveryDeclaredFault
      \/ ContinuedDeclaredFault
      \/ NewDeclaredFault

RecoveredSector(state, decl, missedPost) ==
  (*************************************************************************)
  (* A RecoveredSector occurs when a sector is known to be faulty and      *) 
  (* declared recovered (and the subsequent WindowPoSt is not failed.      *)
  (*************************************************************************)
  state = faulty /\ decl = recovered /\ ~missedPost

(***************************************************************************)
(* PreCommit                                                               *)
(***************************************************************************)

SectorPreCommitOnChainInfo ==
  (*************************************************************************)
  (* Input to PreCommit method                                             *)
  (*************************************************************************)
  [
    RegisteredProof: RegisteredProofs \union {"wrong registered proof"},
    SectorNumber: {"SectorID1", "SectorID2"},
    SealCid: {"SealCID"},
    SealRandEpoch: {
      "BeforeMaxSealDuration or CurrentOrFutureEpoch",
      "Valid"
    },
    DealIDs: {<<>>, <<"deal">>, <<"invalid deal">>, <<"deal1", "deal2">>},
    Expiration: {
      "LessMinSectorLifeTime or MoreMaxSectorLifeTime",
      "Valid"
    }
  ]

ValidPreCommitOnChainInfo(info, ids) ==
  (*************************************************************************)
  (* Validating inputs to PreCommit method                                 *)
  (* - info.RegisteredProof is valid                                       *)
  (* - info.SectorNumber is not in use                                     *)
  (* - info.SealRandEpoch is not between MaxSealDurantion and Current-1    *)
  (* - info.Expiration is not between Min and Max SectorLifetime           *)
  (*************************************************************************)
  /\ info.RegisteredProof \in RegisteredProofs
  /\ ~(info.SectorNumber \in ids)
  /\ info.SealRandEpoch /= "BeforeMaxSealDuration or CurrentOrFutureEpoch"
  /\ info.Expiration /= "LessMinSectorLifeTime or MoreMaxSectorLifeTime"

(***************************************************************************)
(* Filecoin Application                                                    *)
(***************************************************************************)

(*--algorithm faults
variables
  sectorState \in SectorStates,
    (***********************************************************************)
    (* The state of a sector at the beginning of a method call.            *)
    (***********************************************************************)

  sectorStateNext = NULLSTATE,
    (***********************************************************************)
    (* The state of a sector at the end of a method call.                  *)
    (***********************************************************************)

  sectorStateError = NOERROR,
    (***********************************************************************)
    (* The error from an invalid sector state transition.                  *)
    (***********************************************************************)
    
  declaration \in Declarations \union { NULLDECL },
    (***********************************************************************)
    (* The declaration of a sector at the beginning of a method call.      *)
    (***********************************************************************)

  declarationNext = NULLDECL,
    (***********************************************************************)
    (* The declaration of a sector at the end of a method call.            *)
    (***********************************************************************)

  minerSectorIDs \in {{}, {"SectorID1"}},
    (***********************************************************************)
    (* SectorIDs currently in use.                                         *)
    (***********************************************************************)

  minerSectorIDsNext = {},
    (***********************************************************************)
    (* Updated set of SectorIDs at the end of a method call.               *)
    (***********************************************************************)

  failedPoSts \in 0..2,
    (***********************************************************************)
    (* The number of consecutive post failed.                              *)
    (***********************************************************************)

  skippedFault \in BOOLEAN,
    (***********************************************************************)
    (* The flag that indicates if a post proof fails.                      *)
    (***********************************************************************)

  penalties = ZERO,
    (***********************************************************************)
    (* The penalty amount paid at the end of a method call.                *)
    (***********************************************************************)

  methodError = NOERROR,
    (***********************************************************************)
    (* The error from an invalid method execution.                         *)
    (***********************************************************************)

  methodCalled = NULLMETHOD;
    (***********************************************************************)
    (* The last method called.                                             *)
    (***********************************************************************)

(***************************************************************************)
(* Blockchain                                                              *)
(* A miner can take (in this model), one action per epoch.                 *)
(***************************************************************************)
fair+ process miner = "miner"
variables epoch = 0
begin
  Blockchain:
    while epoch < 12 do
      epoch := epoch + 1;
      Block:
        either
          PreCommit:
            methodCalled := "PreCommit";
            if sectorState = clear /\ declaration = NULLDECL then
              \* Mark sector as committed
              with sectorInfo \in SectorPreCommitOnChainInfo do
                if ValidPreCommitOnChainInfo(sectorInfo, minerSectorIDs) then
                  sectorStateNext := precommit;
                  minerSectorIDsNext := minerSectorIDs \union {sectorInfo.SectorNumber};
                else
                  methodError := "invalid precommit"
                end if;
              end with;
            else
              sectorStateError := "invalid precommit";
            end if;
        or
          Commit:
            methodCalled := "Commit";
            if sectorState = precommit /\ declaration = NULLDECL then
              \* Mark sector as active
              sectorStateNext := active;
            else
              sectorStateError := "invalid commit";
            end if;   
        or
          DeclareFault:
            methodCalled := "DeclareFault";
            \* Declare active sector as faulted
            if sectorState = active /\ declaration = NULLDECL then
              declarationNext := faulted;
            \* Declare recovered faulty sector as faulted
            elsif sectorState = faulty /\ declaration = recovered then
              declarationNext := faulted;                            
            else
              sectorStateError := "invalid declare fault";
            end if;
        or
          DeclareRecovery:
            methodCalled := "DeclareRecovery";
            if sectorState = faulty /\ declaration = NULLDECL then
              declarationNext := recovered;
            else
              sectorStateError := "invalid declare recovery";
            end if;
        or
          TerminateSector:
            methodCalled := "TerminateSector";
            if /\ sectorState \in {faulty, active}
               /\ declaration \in {faulted, recovered, NULLDECL} then
              sectorStateNext := done;
              penalties := TF;
            else
              sectorStateError := "invalid declare recovery";
            end if;
        or
          WindowPoSt:
            methodCalled := "WindowPoSt";
            if \/ (sectorState = active /\ declaration \in { NULLDECL, faulted })
               \/ sectorState = faulty then

              \* - skipped faults
              \* - failed recovery
              if RecoveredSector(sectorState, declaration, skippedFault) then
                sectorStateNext := active;

              elsif SkippedFault(sectorState, declaration, skippedFault) then
                if sectorState = active then
                  sectorStateNext := faulty;
                end if;
                penalties := SP;

              \* - continued faults
              \* - recovered fault reported faulty again
              \* - new declared faults
              elsif DeclaredFault(sectorState, declaration) then
                if sectorState = active then
                  sectorStateNext := faulty;
                end if;
                penalties := FF;
              \* - recovered
              end if;

              \* Update faults counter when the sector is faulty
              \* either the sector is faulty already
              \*     or the sector is found to be faulty
              if /\ sectorState = faulty
                 /\ sectorStateNext \in {NULLSTATE, faulty} then
                failedPoSts := failedPoSts + 1;
              else
                failedPoSts := 0;
              end if;

              \* Apply penalties
              ApplyPenalty:
                if failedPoSts >= 3 then
                  penalties := TF;
                  sectorStateNext := done;
                end if;
            else
              sectorStateError := "invalid window post";
            end if;
            \* TODO: Handle honest termination

        end either;

        \* Reset to initial conditions
        End:
          if sectorStateNext /= NULLSTATE then
            sectorState := sectorStateNext;
          end if;
          if minerSectorIDsNext /= {} then
            minerSectorIDs := minerSectorIDsNext;
            minerSectorIDsNext := {};
          end if;
          if methodCalled = "WindowPoSt" then
            declaration := NULLDECL;
          else
            declaration := declarationNext;
          end if;
          if sectorState = clear /\ sectorState = done then
            failedPoSts := 0;
          end if;
          methodCalled := NULLMETHOD;
          declarationNext := NULLDECL;
          sectorStateNext := NULLSTATE;
          penalties := ZERO;

          \* Reset errors
          sectorStateError := NOERROR;
          methodError := NOERROR;
          with x \in BOOLEAN  do
            skippedFault := x;
          end with; 

    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION

\* END TRANSLATION

(***************************************************************************)
(* Invariants********                                                      *)
(***************************************************************************)
MessageExecuted == pc["miner"] = "End"
NoStateTransitionError == sectorStateError = NOERROR
BadInputs == methodError /= NOERROR
NoErrors == NoStateTransitionError /\ ~BadInputs
MessageSucceeded == MessageExecuted => NoErrors
MessageFailed == MessageExecuted => ~NoErrors

MessageInvariants ==
  (*************************************************************************)
  (* Messages must valid transitions or must trigger errors.               *)
  (*************************************************************************)
  LET
    PackedTransition ==
      T(methodCalled, sectorState, sectorStateNext,
      declaration, declarationNext, penalties)

    ValidTransition == PackedTransition \in Transitions
    ValidTransitionNoError ==  ValidTransition /\ NoStateTransitionError
    InvalidMessageHaveError == ~ValidTransition /\ ~NoStateTransitionError
  IN MessageExecuted =>
    \/ ValidTransitionNoError
    \/ InvalidMessageHaveError
    \/ BadInputs

SectorIDInvariants == LET
  (*************************************************************************)
  (* SectorIDs can only be assigned if not currently in use                *)
  (*************************************************************************)
    NewId == Cardinality(minerSectorIDsNext) > Cardinality(minerSectorIDs)
    IdRemoved == Cardinality(minerSectorIDsNext) < Cardinality(minerSectorIDs)

    NewIdOnPrecommitOnly ==
      MessageSucceeded /\ methodCalled = "PreCommit" <=> NewId

  IN NewIdOnPrecommitOnly

PenaltiesInvariants ==
  (*************************************************************************)
  (* Each fault has assigned a penalty.                                    *)
  (*************************************************************************)
  LET
    DeclaredFaultsPayFF ==
      (*********************************************************************)
      (* DeclaredFaults pay FF at WindowPoSt time when the sector is not   *)
      (* terminated.                                                       *)
      (*********************************************************************)
      LET
        DeclaredFaultsCandidates == 
          {s \in Transitions:
            /\ s.method = "WindowPoSt"
            /\ s.stateNext /= done
            /\ DeclaredFault(s.state, s.decl)
            /\ s.penalties = FF}
      IN DeclaredFaultsCandidates = {s \in Transitions : s.penalties = FF}
            
    SkippedFaultsPaySP ==
      (*********************************************************************)
      (* SkippedFaults pay SP at WindowPoSt time when the sector is not    *)
      (* terminated.                                                       *)
      (*********************************************************************)
      LET
        SkippedFaultsCandidates == 
          {t \in Transitions: 
            /\ t.method = "WindowPoSt"
            /\ t.stateNext /= done
            /\ SkippedFault(t.state, t.decl, TRUE)
            /\ t.penalties = SP}
      IN SkippedFaultsCandidates = {s \in Transitions : s.penalties = SP}
  IN DeclaredFaultsPayFF /\ SkippedFaultsPaySP

=============================================================================