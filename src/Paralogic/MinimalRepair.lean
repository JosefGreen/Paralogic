import Paralogic.Repair

/-!
Minimal repair and revision.

This module starts the belief-revision/minimal-change lane with a small,
checked preferential semantics.  It is deliberately finite and modest: it
shows that a repair obligation or acceptability condition need not determine a
unique minimal repair path.
-/

namespace Paralogic

structure RepairRevisionFrame : Type 1 where
  State : Type
  acceptable : State -> Prop
  leq : State -> State -> Prop

def StrictlyPreferred (frame : RepairRevisionFrame)
    (candidate incumbent : frame.State) : Prop :=
  And (frame.leq candidate incumbent)
    (Not (frame.leq incumbent candidate))

def MinimalAcceptableRepair (frame : RepairRevisionFrame)
    (state : frame.State) : Prop :=
  And (frame.acceptable state)
    (forall candidate : frame.State,
      frame.acceptable candidate ->
        Not (StrictlyPreferred frame candidate state))

def HasMinimalRepair (frame : RepairRevisionFrame) : Prop :=
  Exists (fun state : frame.State => MinimalAcceptableRepair frame state)

def HasUniqueMinimalRepair (frame : RepairRevisionFrame) : Prop :=
  Exists (fun selected : frame.State =>
    And (MinimalAcceptableRepair frame selected)
      (forall candidate : frame.State,
        MinimalAcceptableRepair frame candidate -> candidate = selected))

theorem unique_minimal_implies_minimal
    (frame : RepairRevisionFrame)
    (h : HasUniqueMinimalRepair frame) :
    HasMinimalRepair frame := by
  cases h with
  | intro selected hSelected =>
      exact Exists.intro selected hSelected.left

theorem best_acceptable_unique_minimal
    (frame : RepairRevisionFrame)
    (selected : frame.State)
    (hAccept : frame.acceptable selected)
    (hBest : forall candidate : frame.State,
      frame.acceptable candidate -> frame.leq selected candidate)
    (hAntisymm : forall left right : frame.State,
      frame.leq left right -> frame.leq right left -> left = right) :
    HasUniqueMinimalRepair frame := by
  classical
  refine Exists.intro selected ?_
  constructor
  · constructor
    · exact hAccept
    · intro candidate hCandidate hStrict
      exact hStrict.right (hBest candidate hCandidate)
  · intro candidate hMinimal
    have hSelectedLeq : frame.leq selected candidate :=
      hBest candidate hMinimal.left
    by_cases hCandidateLeq : frame.leq candidate selected
    · exact hAntisymm candidate selected hCandidateLeq hSelectedLeq
    · exact False.elim
        (hMinimal.right selected hAccept
          (And.intro hSelectedLeq hCandidateLeq))

inductive TwoRepairChoice where
  | left
  | right
  deriving DecidableEq, Repr

def twoRepairFrame : RepairRevisionFrame :=
  { State := TwoRepairChoice
    acceptable := fun _ => True
    leq := fun candidate incumbent => candidate = incumbent }

theorem twoRepair_left_minimal :
    MinimalAcceptableRepair twoRepairFrame TwoRepairChoice.left := by
  constructor
  · exact True.intro
  · intro candidate _ hStrict
    exact hStrict.right hStrict.left.symm

theorem twoRepair_right_minimal :
    MinimalAcceptableRepair twoRepairFrame TwoRepairChoice.right := by
  constructor
  · exact True.intro
  · intro candidate _ hStrict
    exact hStrict.right hStrict.left.symm

theorem twoRepair_has_minimal :
    HasMinimalRepair twoRepairFrame :=
  Exists.intro TwoRepairChoice.left twoRepair_left_minimal

theorem twoRepair_not_unique_minimal :
    Not (HasUniqueMinimalRepair twoRepairFrame) := by
  intro hUnique
  cases hUnique with
  | intro selected hSelected =>
      have hLeft : TwoRepairChoice.left = selected :=
        hSelected.right TwoRepairChoice.left twoRepair_left_minimal
      have hRight : TwoRepairChoice.right = selected :=
        hSelected.right TwoRepairChoice.right twoRepair_right_minimal
      have hEq : TwoRepairChoice.left = TwoRepairChoice.right :=
        Eq.trans hLeft hRight.symm
      cases hEq

inductive RankedRepairState where
  | unrepaired
  | underRepaired
  | adequate
  | overRepaired
  deriving DecidableEq, Repr

def RankedRepairAcceptable : RankedRepairState -> Prop
  | RankedRepairState.adequate => True
  | RankedRepairState.overRepaired => True
  | _ => False

def RankedRepairLeq
    (candidate incumbent : RankedRepairState) : Prop :=
  match candidate, incumbent with
  | RankedRepairState.adequate, _ => True
  | RankedRepairState.overRepaired, RankedRepairState.overRepaired => True
  | RankedRepairState.overRepaired, RankedRepairState.underRepaired => True
  | RankedRepairState.overRepaired, RankedRepairState.unrepaired => True
  | RankedRepairState.underRepaired, RankedRepairState.underRepaired => True
  | RankedRepairState.underRepaired, RankedRepairState.unrepaired => True
  | RankedRepairState.unrepaired, RankedRepairState.unrepaired => True
  | _, _ => False

def rankedRepairFrame : RepairRevisionFrame :=
  { State := RankedRepairState
    acceptable := RankedRepairAcceptable
    leq := RankedRepairLeq }

theorem rankedRepair_adequate_minimal :
    MinimalAcceptableRepair rankedRepairFrame RankedRepairState.adequate := by
  constructor
  · exact True.intro
  · intro candidate hAccept hStrict
    cases candidate <;>
      simp [rankedRepairFrame, RankedRepairAcceptable, RankedRepairLeq,
        StrictlyPreferred] at hAccept hStrict

theorem rankedRepair_over_not_minimal :
    Not (MinimalAcceptableRepair rankedRepairFrame
      RankedRepairState.overRepaired) := by
  intro hMinimal
  have hStrict :
      StrictlyPreferred rankedRepairFrame RankedRepairState.adequate
        RankedRepairState.overRepaired := by
    constructor
    · exact True.intro
    · intro hLeq
      cases hLeq
  exact hMinimal.right RankedRepairState.adequate True.intro hStrict

theorem rankedRepair_has_minimal :
    HasMinimalRepair rankedRepairFrame :=
  Exists.intro RankedRepairState.adequate rankedRepair_adequate_minimal

theorem rankedRepair_adequate_best_acceptable :
    forall candidate : rankedRepairFrame.State,
      rankedRepairFrame.acceptable candidate ->
        rankedRepairFrame.leq RankedRepairState.adequate candidate := by
  intro candidate hAccept
  cases candidate <;>
    simp [rankedRepairFrame, RankedRepairAcceptable, RankedRepairLeq] at hAccept ⊢

theorem rankedRepair_leq_antisymmetric :
    forall left right : rankedRepairFrame.State,
      rankedRepairFrame.leq left right ->
        rankedRepairFrame.leq right left -> left = right := by
  intro left right hLeftRight hRightLeft
  cases left <;> cases right <;>
    simp [rankedRepairFrame, RankedRepairLeq] at hLeftRight hRightLeft ⊢

theorem rankedRepair_unique_minimal_from_best :
    HasUniqueMinimalRepair rankedRepairFrame :=
  best_acceptable_unique_minimal rankedRepairFrame RankedRepairState.adequate
    True.intro rankedRepair_adequate_best_acceptable
    rankedRepair_leq_antisymmetric

theorem rankedRepair_has_unique_minimal :
    HasUniqueMinimalRepair rankedRepairFrame := by
  refine Exists.intro RankedRepairState.adequate ?_
  constructor
  · exact rankedRepair_adequate_minimal
  · intro candidate hMinimal
    cases candidate
    · cases hMinimal.left
    · cases hMinimal.left
    · rfl
    · exact False.elim (rankedRepair_over_not_minimal hMinimal)

inductive RepairRevisionAction where
  | noAction
  | partialAction
  | targetedAction
  | excessiveAction
  deriving DecidableEq, Repr

def repairActionResult :
    RepairRevisionAction -> RankedRepairState
  | RepairRevisionAction.noAction => RankedRepairState.unrepaired
  | RepairRevisionAction.partialAction => RankedRepairState.underRepaired
  | RepairRevisionAction.targetedAction => RankedRepairState.adequate
  | RepairRevisionAction.excessiveAction => RankedRepairState.overRepaired

def RepairActionSuccessful (action : RepairRevisionAction) : Prop :=
  rankedRepairFrame.acceptable (repairActionResult action)

def RepairActionMinimal (action : RepairRevisionAction) : Prop :=
  MinimalAcceptableRepair rankedRepairFrame (repairActionResult action)

def RepairActionConservative (action : RepairRevisionAction) : Prop :=
  Not (repairActionResult action = RankedRepairState.overRepaired)

structure RepairRevisionPostulates
    (action : RepairRevisionAction) : Prop where
  success : RepairActionSuccessful action
  minimal : RepairActionMinimal action
  conservative : RepairActionConservative action

theorem targetedRepair_satisfies_revision_postulates :
    RepairRevisionPostulates RepairRevisionAction.targetedAction := by
  constructor
  · exact True.intro
  · exact rankedRepair_adequate_minimal
  · intro hEq
    cases hEq

theorem partialRepair_not_successful :
    Not (RepairActionSuccessful RepairRevisionAction.partialAction) := by
  intro hSuccess
  cases hSuccess

theorem doNothingRepair_not_successful :
    Not (RepairActionSuccessful RepairRevisionAction.noAction) := by
  intro hSuccess
  cases hSuccess

theorem excessiveRepair_successful_not_minimal :
    And (RepairActionSuccessful RepairRevisionAction.excessiveAction)
      (Not (RepairActionMinimal RepairRevisionAction.excessiveAction)) := by
  constructor
  · exact True.intro
  · exact rankedRepair_over_not_minimal

theorem excessiveRepair_not_conservative :
    Not (RepairActionConservative RepairRevisionAction.excessiveAction) := by
  intro hConservative
  exact hConservative rfl

theorem excessiveRepair_not_revision_postulates :
    Not (RepairRevisionPostulates RepairRevisionAction.excessiveAction) := by
  intro hPostulates
  exact excessiveRepair_not_conservative hPostulates.conservative

structure DiagnosisGuidedRepairRevision {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (action : RepairRevisionAction) : Prop where
  diagnosis : RepairDiagnosisSatisfied profile
  revision : RepairRevisionPostulates action

theorem diagnosis_guided_repair_warrants_obligation {M : SigmaModel}
    {profile : RepairDiagnosisProfile M}
    {action : RepairRevisionAction}
    (guided : DiagnosisGuidedRepairRevision profile action) :
    RepairObligationBridgeSem profile.bridge profile.institution
      profile.group :=
  RepairDiagnosisProfile_to_repairObligation profile guided.diagnosis

def repairBridgeOnlyTargetedRevision :
    DiagnosisGuidedRepairRevision repairBridgeOnlyDiagnosis
      RepairRevisionAction.targetedAction :=
  { diagnosis := repairBridgeOnlyDiagnosis_satisfied
    revision := targetedRepair_satisfies_revision_postulates }

theorem repairBridgeOnlyTargetedRevision_warrants_obligation :
    RepairObligationBridgeSem (M := repairBridgeOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  diagnosis_guided_repair_warrants_obligation
    repairBridgeOnlyTargetedRevision

inductive RepairPostulateState where
  | failed
  | adequate
  | redundant
  | overreach
  deriving DecidableEq, Repr

def RepairPostulateAcceptable : RepairPostulateState -> Prop
  | RepairPostulateState.adequate => True
  | RepairPostulateState.redundant => True
  | RepairPostulateState.overreach => True
  | RepairPostulateState.failed => False

def RepairPostulateLeq
    (candidate incumbent : RepairPostulateState) : Prop :=
  match candidate, incumbent with
  | RepairPostulateState.adequate, RepairPostulateState.adequate => True
  | RepairPostulateState.adequate, RepairPostulateState.redundant => True
  | RepairPostulateState.adequate, RepairPostulateState.failed => True
  | RepairPostulateState.redundant, RepairPostulateState.redundant => True
  | RepairPostulateState.redundant, RepairPostulateState.failed => True
  | RepairPostulateState.overreach, RepairPostulateState.overreach => True
  | RepairPostulateState.overreach, RepairPostulateState.failed => True
  | RepairPostulateState.failed, RepairPostulateState.failed => True
  | _, _ => False

def repairPostulateFrame : RepairRevisionFrame :=
  { State := RepairPostulateState
    acceptable := RepairPostulateAcceptable
    leq := RepairPostulateLeq }

theorem postulate_adequate_minimal :
    MinimalAcceptableRepair repairPostulateFrame
      RepairPostulateState.adequate := by
  constructor
  · exact True.intro
  · intro candidate hAccept hStrict
    cases candidate <;>
      simp [repairPostulateFrame, RepairPostulateAcceptable,
        RepairPostulateLeq, StrictlyPreferred] at hAccept hStrict

theorem postulate_overreach_minimal :
    MinimalAcceptableRepair repairPostulateFrame
      RepairPostulateState.overreach := by
  constructor
  · exact True.intro
  · intro candidate hAccept hStrict
    cases candidate <;>
      simp [repairPostulateFrame, RepairPostulateAcceptable,
        RepairPostulateLeq, StrictlyPreferred] at hAccept hStrict

theorem postulate_redundant_not_minimal :
    Not (MinimalAcceptableRepair repairPostulateFrame
      RepairPostulateState.redundant) := by
  intro hMinimal
  have hStrict :
      StrictlyPreferred repairPostulateFrame RepairPostulateState.adequate
        RepairPostulateState.redundant := by
    constructor
    · exact True.intro
    · intro hLeq
      cases hLeq
  exact hMinimal.right RepairPostulateState.adequate True.intro hStrict

inductive RepairPostulateAction where
  | failedAction
  | adequateAction
  | redundantAction
  | overreachAction
  deriving DecidableEq, Repr

def repairPostulateActionResult :
    RepairPostulateAction -> RepairPostulateState
  | RepairPostulateAction.failedAction => RepairPostulateState.failed
  | RepairPostulateAction.adequateAction => RepairPostulateState.adequate
  | RepairPostulateAction.redundantAction => RepairPostulateState.redundant
  | RepairPostulateAction.overreachAction => RepairPostulateState.overreach

def RepairPostulateActionSuccessful
    (action : RepairPostulateAction) : Prop :=
  repairPostulateFrame.acceptable (repairPostulateActionResult action)

def RepairPostulateActionMinimal
    (action : RepairPostulateAction) : Prop :=
  MinimalAcceptableRepair repairPostulateFrame
    (repairPostulateActionResult action)

def RepairPostulateActionConservative
    (action : RepairPostulateAction) : Prop :=
  Not (repairPostulateActionResult action = RepairPostulateState.overreach)

structure RepairPostulateIndependencePackage
    (action : RepairPostulateAction) : Prop where
  success : RepairPostulateActionSuccessful action
  minimal : RepairPostulateActionMinimal action
  conservative : RepairPostulateActionConservative action

theorem adequateAction_satisfies_independence_package :
    RepairPostulateIndependencePackage
      RepairPostulateAction.adequateAction := by
  constructor
  · exact True.intro
  · exact postulate_adequate_minimal
  · intro hEq
    cases hEq

theorem redundantAction_success_conservative_not_minimal :
    And (RepairPostulateActionSuccessful
        RepairPostulateAction.redundantAction)
      (And (RepairPostulateActionConservative
          RepairPostulateAction.redundantAction)
        (Not (RepairPostulateActionMinimal
          RepairPostulateAction.redundantAction))) := by
  constructor
  · exact True.intro
  · constructor
    · intro hEq
      cases hEq
    · exact postulate_redundant_not_minimal

theorem overreachAction_success_minimal_not_conservative :
    And (RepairPostulateActionSuccessful
        RepairPostulateAction.overreachAction)
      (And (RepairPostulateActionMinimal
          RepairPostulateAction.overreachAction)
        (Not (RepairPostulateActionConservative
          RepairPostulateAction.overreachAction))) := by
  constructor
  · exact True.intro
  · constructor
    · exact postulate_overreach_minimal
    · intro hConservative
      exact hConservative rfl

theorem failedAction_conservative_not_successful :
    And (RepairPostulateActionConservative
        RepairPostulateAction.failedAction)
      (Not (RepairPostulateActionSuccessful
        RepairPostulateAction.failedAction)) := by
  constructor
  · intro hEq
    cases hEq
  · intro hSuccess
    cases hSuccess

end Paralogic
