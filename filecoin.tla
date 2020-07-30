----------------------------- MODULE filecoin -------------------------------

EXTENDS TLC, Integers

done == "done"
active == "active"
precommit == "precommit"
faulty == "faulty"
clear == "clear"

faulted == "faulted"
recovered == "recovered"
NULLDECL == "null declaration"
methods == {"PreCommit", "ProveCommit", "DeclareFault", "DeclareRecovery", "WindowPoSt", "TerminateSector"}

ZERO == "zero"
TF == "TF"
FF == "FF"
SP == "SP"

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

SectorStates == {clear, precommit, active, faulty, done}
  (*************************************************************************)
  (* The set of all sector states.                                         *)
  (*************************************************************************)

Declarations == {recovered, faulted}
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
    (* DeclareFault: New Declared Fault                                    *)
    (* An active sector is declared faulted.                               *)
    (***********************************************************************)
    T("DeclareFault", active, active, NULLDECL, faulted, ZERO),

    (***********************************************************************)
    (* DeclareFault: Failed Recovery Declared Fault                        *)
    (* A faulty sector that is declared as recovered is now redeclared as  *)
    (* faulty.                                                             *)
    (***********************************************************************)
    T("DeclareFault", faulty, faulty, recovered, faulted, ZERO),

    T("DeclareRecovery", faulty, faulty, NULLDECL, recovered, ZERO),
    T("DeclareRecovery", faulty, faulty, faulted, recovered, ZERO),
    T("DeclareRecovery", active, active, faulted, recovered, ZERO),

    (***********************************************************************)
    (* WindowPoSt: Honest case                                             *)
    (* An active sector remains active.                                    *)
    (***********************************************************************)
    T("WindowPoSt", active, active, NULLDECL, NULLDECL, ZERO),
    T("ProvingDeadline", active, active, NULLDECL, NULLDECL, ZERO),
    
    (***********************************************************************)
    (* WindowPoSt: Continued Fault                                         *)
    (* A faulty sector remains faulty in absence of declarations.          *)
    (***********************************************************************)
    T("WindowPoSt", faulty, faulty, NULLDECL, NULLDECL, FF),
    T("ProvingDeadline", faulty, faulty, NULLDECL, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: New Declared Fault                                      *)
    (* An active sector that is declared faulted becomes faulty.           *)
    (***********************************************************************)
    T("WindowPoSt", active, faulty, faulted, NULLDECL, FF),
    T("ProvingDeadline", active, faulty, faulted, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: Failed Recovery Declared Fault                          *)
    (* A faulty sector declared as recovered and then declared again as    *)
    (* faulted becomes faulty                                              *)
    (***********************************************************************)
    T("WindowPoSt", faulty, faulty, faulted, NULLDECL, FF),
    T("ProvingDeadline", faulty, faulty, faulted, NULLDECL, FF),

    (***********************************************************************)
    (* WindowPoSt: Active Skipped Faults                                   *)
    (* An active sector that is not declared faulted becomes faulty.       *)
    (***********************************************************************)
    T("WindowPoSt", active, faulty, NULLDECL, NULLDECL, SP),
    T("ProvingDeadline", active, faulty, NULLDECL, NULLDECL, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Skipped Fault                                 *)
    (* A faulty sector is declared recovered and then fails the proof      *)
    (* becomes faulty.                                                     *)
    (***********************************************************************)
    T("WindowPoSt", faulty, faulty, recovered, NULLDECL, SP),
    T("ProvingDeadline", faulty, faulty, recovered, NULLDECL, SP),

    (***********************************************************************)
    (* WindowPoSt: Recovered Sector                                        *)
    (* A faulty sector declared as recovered becomes active.               *)
    (***********************************************************************)
    T("WindowPoSt", faulty, active, recovered, NULLDECL, FF)
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
  [
    method: {"ProvingDeadline"},
    state: {faulty},
    stateNext: {done},
    decl: {NULLDECL, recovered, faulted},
    declNext: {NULLDECL},
    penalties: {TF}
  ]

TransitionsState ==
  {[state |-> x.state, decl |-> x.decl]: x \in Transitions}
TransitionsStateNext ==
  {[state |-> x.stateNext, decl |-> x.declNext]: x \in Transitions}
ValidStates == TransitionsState \union TransitionsStateNext

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
    FailedRecoveryDeclaredFault == state = faulty /\ decl = faulted
      (*********************************************************************)
      (* A faulty sector is still declared faulty, after being recovered.  *)
      (*********************************************************************)

    ContinuedDeclaredFault == state = faulty /\ decl = NULLDECL
      (*********************************************************************)
      (* A sector is faulty and continues being so.                        *)
      (*********************************************************************)

    NewDeclaredFault == state = active /\ decl = faulted
      (*********************************************************************)
      (* A sector is active and declared as faulty.                        *)
      (*********************************************************************)

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
(* Filecoin Application                                                    *)
(***************************************************************************)
(*--algorithm filecoin

variables
  collateral \in {0, 1, 2},
  st \in ValidStates,
  sectorState = st.state, \* \in SectorStates,
    (***********************************************************************)
    (* The state of a sector at the beginning of a method call.            *)
    (***********************************************************************)

  declaration = st.decl, \* \in Declarations \union {NULLDECL},
    (***********************************************************************)
    (* The declaration of a sector at the beginning of a method call.      *)
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
        if sectorState = clear /\ declaration = NULLDECL then
          sectorState := precommit;
        end if;
    or
      DeclareRecovery:
        if \/ sectorState = active /\ declaration = faulted
           \/ sectorState = faulty /\ declaration = faulted then
          declaration := recovered;
        end if;
    or
      DeclareFault:
        if \/ (sectorState = active /\ declaration = NULLDECL)
           \/ (sectorState = faulty /\ declaration = recovered) then
          if collateral > 1 then
            declaration := faulted;
          end if;
        end if;
    or
      Commit:
        if sectorState = precommit /\ declaration = NULLDECL then
          sectorState := active;
        end if;
    or
      TerminateSector:
        if /\ sectorState \in {faulty, active}
           /\ declaration \in {faulted, recovered, NULLDECL}
           /\ collateral > 2 then
          sectorState := done;
          declaration := NULLDECL;
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
        if \/ (sectorState = active /\ declaration \in {NULLDECL, faulted})
           \/ (sectorState = faulty) then

          with skippedFault \in BOOLEAN do
            if RecoveredSector(sectorState, declaration, skippedFault) then
              sectorState := active;
              penalties := FF;
              collateral := collateral - 1;
            elsif SkippedFault(sectorState, declaration, skippedFault) then
              sectorState := faulty;
              penalties := SP;
              collateral := collateral - 2;
            elsif DeclaredFault(sectorState, declaration) then
              sectorState := faulty;
              penalties := FF;
              collateral := collateral - 1;
            end if;
            declaration := NULLDECL;
          end with;

        end if;
    or
      ProvingDeadline:
        if \/ (sectorState = active /\ declaration \in {NULLDECL, faulted})
           \/ (sectorState = faulty) then

          with missedPoSt \in BOOLEAN do
            if failedPoSt = 13 /\ sectorState = faulty then
              sectorState := done;
              penalties := TF;
              collateral := collateral - 2
            elsif \/ RecoveredSector(sectorState, declaration, missedPoSt)
                  \/ SkippedFault(sectorState, declaration, TRUE) then
              sectorState := faulty;
              penalties := SP;
              collateral := collateral - 2
            elsif DeclaredFault(sectorState, declaration) then
              sectorState := faulty;
              penalties := FF;
              collateral := collateral - 1
            end if;
          end with;
          declaration := NULLDECL;
        end if;
    end either;

end algorithm; *)
\* BEGIN TRANSLATION

\* END TRANSLATION

CurrState == T(pc, sectorState, sectorState', declaration, declaration', penalties') 

ValidMessage == CurrState \in Transitions

ValidMessageProperty == 
  (*************************************************************************)
  (* Messages must valid transitions or must trigger errors.               *)
  (*************************************************************************)
  [][ValidMessage]_<<sectorState, declaration, penalties>>

TransitionsInvariants ==
  (*************************************************************************)
  (* All final states are valid initial states and viceversa.              *)
  (*************************************************************************)
  LET
    Initial ==
      TransitionsState \ {[state |-> clear, decl |-> NULLDECL]} 
    Final ==
      TransitionsStateNext \ {[state |-> done, decl |-> NULLDECL]} 
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
            /\ s.stateNext /= done
            /\ \/ DeclaredFault(s.state, s.decl)
               \/ RecoveredSector(s.state, s.decl, FALSE)
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
            /\ \/ t.method = "ProvingDeadline" /\ t.stateNext = done
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
            /\ t.stateNext /= done
            /\ SkippedFault(t.state, t.decl, TRUE)
            /\ t.penalties = SP}
      IN SkippedFaultsCandidates = {s \in Transitions : s.penalties = SP}
  IN DeclaredFaultsAndRecoveredPayFF
    /\ SkippedFaultsPaySP
    /\ TerminationFaultsPayTF

ASSUME PenaltiesInvariants

CollateralInvariants ==
  pc = "Done" => collateral >= 0

=============================================================================
