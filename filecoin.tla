----------------------------- MODULE filecoin -------------------------------

EXTENDS TLC, Integers

clear == "clear"
precommit == "precommit"
unproven == "unproven"
active == "active"
faulty == "faulty"
recovering == "recovering"
terminated == "terminated"

methods == {"PreCommit", "ProveCommit", "DeclareFault", "DeclareRecovery", "WindowPoSt", "TerminateSector"}

ZERO == "zero"
TF == "TF"
FF == "FF"
SP == "SP"

T(method, state, stateNext, pen) ==
  (*************************************************************************)
  (* Utility that packs a list into a struct.                              *)
  (*************************************************************************)
  [
    method |-> method,
    state |-> state,
    stateNext |-> stateNext,
    penalties |-> pen
  ]

(***************************************************************************)
(* StorageMiner Actor                                                      *)
(***************************************************************************)

SectorStates ==
    {clear, precommit, unproven, active, faulty, recovering, terminated}
  (*************************************************************************)
  (* The set of all sector states.                                         *)
  (*************************************************************************)

Transitions ==
  (*************************************************************************)
  (* The set of all valid StorageMiner state transitions.                  *)
  (* - `method`: the Actor method called                                   *)
  (* - `state`: the sector state at the beginning of the call              *)
  (* - `stateNext`: the sector state at the end of the call                *)
  (* - `penalties`: the penalty paid by the end of the call                *)
  (*************************************************************************)
  {
    (***********************************************************************)
    (* Precommit: A clear sector is precommitted (clear ->  precommit).    *)
    (***********************************************************************)
    T("PreCommit", clear, precommit, ZERO),
    
    (***********************************************************************)
    (* Commit: A precommitted sector becomes active (precommit -> active). *)
    (***********************************************************************)
    T("Commit", precommit, active, ZERO),
    
    (***********************************************************************)
    (* DeclareFault: New Declared Fault                                    *)
    (* An active sector is declared faulted.                               *)
    (***********************************************************************)
    T("DeclareFault", active, faulty, ZERO),

    (***********************************************************************)
    (* DeclareFault: Failed Recovery Declared Fault                        *)
    (* A faulty sector that is declared as recovered is now redeclared as  *)
    (* faulty.                                                             *)
    (***********************************************************************)
    T("DeclareFault", recovering, faulty, ZERO),

    T("DeclareRecovery", faulty, recovering, ZERO),

    (***********************************************************************)
    (* WindowPoSt: Honest case                                             *)
    (* An active sector remains active.                                    *)
    (***********************************************************************)
    T("WindowPoSt", active, active, ZERO),
    T("ProvingDeadline", active, active, ZERO),
    
    (***********************************************************************)
    (* WindowPoSt: Continued Fault                                         *)
    (* A faulty sector remains faulty in absence of declarations.          *)
    (***********************************************************************)
    T("WindowPoSt", faulty, faulty, FF),
    T("ProvingDeadline", faulty, faulty, FF),

    (***********************************************************************)
    (* WindowPoSt: New Declared Fault                                      *)
    (* An active sector that is declared faulted becomes faulty.           *)
    (***********************************************************************)
    \* T("WindowPoSt", faulty, faulty, FF),
    \* T("ProvingDeadline", faulty, faulty, FF),

    (***********************************************************************)
    (* WindowPoSt: Failed Recovery Declared Fault                          *)
    (* A faulty sector declared as recovered and then declared again as    *)
    (* faulted becomes faulty                                              *)
    (***********************************************************************)
    \* T("WindowPoSt", faulty, faulty, faulted, NULLDECL, FF),
    \* T("ProvingDeadline", faulty, faulty, faulted, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: Active Skipped Faults                                   *)
    (* An active sector that is not declared faulted becomes faulty.       *)
    (***********************************************************************)
    T("WindowPoSt", active, faulty, SP),
    T("ProvingDeadline", active, faulty, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Skipped Fault                                 *)
    (* A faulty sector is declared recovered and then fails the proof      *)
    (* becomes faulty.                                                     *)
    (***********************************************************************)
    T("WindowPoSt", recovering, faulty, SP),
    T("ProvingDeadline", recovering, faulty, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Sector                                        *)
    (* A faulty sector declared as recovered becomes active.               *)
    (***********************************************************************)
    T("WindowPoSt", recovering, active, FF)
  }
  \union
  (*************************************************************************)
  (* TerminateSector: An active or faulty sector is terminated             *)
  (*************************************************************************)
  [
    method: {"TerminateSector"},
    state: {faulty, active, recovering},
    stateNext: {terminated},
    penalties: {TF}
  ]
  \union 
  [
    method: {"ProvingDeadline"},
    state: {faulty, recovering},
    stateNext: {terminated},
    penalties: {TF}
  ]

TransitionsState ==
  {[state |-> x.state]: x \in Transitions}
TransitionsStateNext ==
  {[state |-> x.stateNext]: x \in Transitions}
ValidStates == TransitionsState \union TransitionsStateNext

(***************************************************************************)
(* Faults                                                                  *)
(***************************************************************************)

SkippedFault(state, missedPoSt) == 
  (*************************************************************************)
  (* A SkippedFault occurs when an active sector or a recovered sector     *)
  (* fails to be proven at WindowPoSt                                      *)
  (*************************************************************************)
  LET 
    ActiveSector == (state = active)
    RecoverSector == (state = recovering)
    ExpectingProof == ActiveSector \/ RecoverSector
  IN ExpectingProof /\ missedPoSt

DeclaredFault(state) == 
  (*************************************************************************)
  (* A DeclaredFault occurs when a sector is known to be faulty.           *)
  (*************************************************************************)
  state = faulty 

RecoveredSector(state, missedPost) ==
  (*************************************************************************)
  (* A RecoveredSector occurs when a sector is known to be faulty and      *) 
  (* declared recovered (and the subsequent WindowPoSt is not failed.      *)
  (*************************************************************************)
  state = recovering /\ ~missedPost

(***************************************************************************)
(* Filecoin Application                                                    *)
(***************************************************************************)
(*--algorithm filecoin

variables
  collateral \in {-1, 0, 1},
  st \in ValidStates,
  sectorState = st.state, \* \in SectorStates,
    (***********************************************************************)
    (* The state of a sector at the beginning of a method call.            *)
    (***********************************************************************)

  penalties = ZERO,
    (***********************************************************************)
    (* The penalty amount paid at the end of a method call.                *)
    (***********************************************************************)

  failedPoSt \in {0, 13};
    (***********************************************************************)
    (* The number of consecutive post failed.                              *)
    (***********************************************************************)

begin
  Block:
    either
      PreCommit:
        if /\ sectorState = clear
           /\ collateral >= 0 then
          sectorState := precommit;
        end if;
    or
      DeclareRecovery:
        if /\ sectorState = faulty 
           /\ collateral >= 0
            then
          sectorState := recovering;
        end if;
    or
      DeclareFault:
        if /\ \/ sectorState = active
              \/ sectorState = recovering
           /\ collateral >= 1 then
            sectorState := faulty;
        end if;
    or
      Commit:
        if /\ sectorState = precommit
           /\ collateral >= 1 then
          sectorState := active;
        end if;
    or
      TerminateSector:
        if /\ sectorState \in {faulty, active} 
           /\ collateral >= 1 then
          sectorState := terminated;
          penalties := TF;

          \* (* the collateral that can be removed is at most the total.         *)
          \* if collateral - 2 > 0 then
          \*   collateral := collateral - 2;
          \* else 
          \*   collateral := 0;
          \* end if;
        end if;
    or
      WindowPoSt:
        if \/ (sectorState = active)
           \/ (sectorState = faulty) then

          with skippedFault \in BOOLEAN do
            if RecoveredSector(sectorState, skippedFault) then
              sectorState := active;
              penalties := FF;
              collateral := collateral - 1;
            elsif SkippedFault(sectorState, skippedFault) then
              sectorState := faulty;
              penalties := SP;
              collateral := collateral - 2;
            elsif DeclaredFault(sectorState) then
              sectorState := faulty;
              penalties := FF;
              collateral := collateral - 1;
            end if;
          end with;

        end if;
    or
      ProvingDeadline:
        if \/ (sectorState = active)
           \/ (sectorState = faulty) then

          with missedPoSt \in BOOLEAN do
            if failedPoSt = 13 /\ sectorState = faulty then
              sectorState := terminated;
              penalties := TF;
              collateral := collateral - 2
            elsif \/ RecoveredSector(sectorState, missedPoSt)
                  \/ SkippedFault(sectorState, TRUE) then
              sectorState := faulty;
              penalties := SP;
              collateral := collateral - 2
            elsif DeclaredFault(sectorState) then
              sectorState := faulty;
              penalties := FF;
              collateral := collateral - 1
            end if;
          end with;
        end if;
    end either;

end algorithm; *)
\* BEGIN TRANSLATION

\* END TRANSLATION

CurrState == T(pc, sectorState, sectorState', penalties') 

ValidMessage == CurrState \in Transitions

ValidMessageProperty == 
  (*************************************************************************)
  (* Messages must valid transitions or must trigger errors.               *)
  (*************************************************************************)
  [][ValidMessage]_<<sectorState, penalties>>

TransitionsInvariants ==
  (*************************************************************************)
  (* All final states are valid initial states and viceversa.              *)
  (*************************************************************************)
  LET
    Initial ==
      TransitionsState \ {[state |-> clear]} 
    Final ==
      TransitionsStateNext \ {[state |-> terminated]} 
  IN Initial = Final

ASSUME TransitionsInvariants 

PenaltiesInvariants ==
  (*************************************************************************)
  (* Each fault has assigned a penalty.                                    *)
  (*************************************************************************)
  LET
    DeclaredFaultsAndRecoveredPayFF ==
      (*********************************************************************)
      (* DeclaredFaults pay FF at WindowPoSt time when the sector is not   *)
      (* terminated. Recovered faults pay FF at successful WindowPoSt.     *)
      (*********************************************************************)
      LET
        DeclaredFaultsCandidates == 
          {s \in Transitions:
            /\ s.method \in {"WindowPoSt", "ProvingDeadline"}
            /\ s.stateNext /= terminated
            /\ \/ DeclaredFault(s.state)
               \/ RecoveredSector(s.state, FALSE)
            /\ s.penalties = FF}
      IN DeclaredFaultsCandidates = {s \in Transitions : s.penalties = FF}

    TerminationFaultsPayTF ==
      (*********************************************************************)
      (* TerminationFaults pay TF at WindowPoSt time when the sector is    *)
      (* terminated or when TerminateSector is called.                     *)
      (*********************************************************************)
      LET 
        TerminationCandidates ==
          {t \in Transitions:
            /\ \/ t.method = "ProvingDeadline" /\ t.stateNext = terminated
               \/ t.method = "TerminateSector"
            /\ t.penalties = TF}
      IN TerminationCandidates = {s \in Transitions : s.penalties = TF }
            
    SkippedFaultsPaySP ==
      (*********************************************************************)
      (* SkippedFaults pay SP at WindowPoSt time when the sector is not    *)
      (* terminated.                                                       *)
      (*********************************************************************)
      LET
        SkippedFaultsCandidates == 
          {t \in Transitions: 
            /\ t.method \in {"WindowPoSt", "ProvingDeadline"}
            /\ t.stateNext /= terminated
            /\ SkippedFault(t.state, TRUE)
            /\ t.penalties = SP}
      IN SkippedFaultsCandidates = {s \in Transitions : s.penalties = SP}
  IN DeclaredFaultsAndRecoveredPayFF
    /\ SkippedFaultsPaySP
    /\ TerminationFaultsPayTF

ASSUME PenaltiesInvariants

CollateralInvariants ==
  /\ pc \in {"ProveCommit", "ProveCommit"} => collateral >= 0
  /\ pc \in {"DeclareFault", "DeclareRecovery"} => collateral >= 1
  /\ pc \in {"TerminateSector"} => collateral >= 2

=============================================================================
