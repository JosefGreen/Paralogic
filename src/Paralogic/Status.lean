/-!
Status labels for Paralogic / ISFT.

These are data labels, not evidence by themselves. A theorem may be called
`MC3Lean` only after a trusted Lean run accepts it.
-/

namespace Paralogic

inductive StatementStatus where
  | definition
  | primitiveAxiom
  | moduleAxiom
  | theorem
  | conjecture
  | proofObligation
  | countermodel
  | empiricalHypothesis
  | normativeBridge
  | implementationClaim
  | heuristic
  | deferredItem
  deriving DecidableEq, Repr

inductive ProofStatus where
  | ps0
  | ps1
  | ps2
  | ps3
  | ps4
  deriving DecidableEq, Repr

inductive MachineStatus where
  | mc0
  | mc1
  | mc2
  | mc3Lean
  | efc
  | efe
  | pyc
  deriving DecidableEq, Repr

inductive EmpiricalStatus where
  | emp0
  | emp1
  | emp2
  | emp3
  | emp4
  | emp5
  deriving DecidableEq, Repr

structure StatusRecord where
  statement : StatementStatus
  proof : ProofStatus
  machine : MachineStatus
  empirical : EmpiricalStatus
  deriving Repr

def leanCheckedEmp0 : StatusRecord :=
  { statement := StatementStatus.theorem
    proof := ProofStatus.ps3
    machine := MachineStatus.mc3Lean
    empirical := EmpiricalStatus.emp0 }

def textProofCandidate : StatusRecord :=
  { statement := StatementStatus.theorem
    proof := ProofStatus.ps2
    machine := MachineStatus.mc2
    empirical := EmpiricalStatus.emp0 }

theorem leanCheckedEmp0_is_not_empirical_validation :
    leanCheckedEmp0.empirical = EmpiricalStatus.emp0 := rfl

theorem proof_ready_candidate_is_not_lean_checked :
    textProofCandidate.machine = MachineStatus.mc2 := rfl

end Paralogic
