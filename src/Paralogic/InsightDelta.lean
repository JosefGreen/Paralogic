import Paralogic.ModelSemantics
import Paralogic.Contradiction

/-!
Insight and Delta outcome calculus.

This module keeps candidate insight, valid insight, false insight, null
insight, and Delta outcomes separate. In particular, Delta resolution is not
truth, finality, repair, or empirical validation.
-/

namespace Paralogic

structure CandidateInsightCase (M : SigmaModel) where
  insight : M.Carrier SortTag.candidateInsight
  candidate : CandidateInsightSem insight

structure TransformableInsightCase (M : SigmaModel) where
  insight : M.Carrier SortTag.candidateInsight
  sourceFrame : M.Carrier SortTag.frame
  targetFrame : M.Carrier SortTag.frame
  candidate : CandidateInsightSem insight
  licensedTransition : LicensedTransitionSem insight sourceFrame targetFrame
  nonTrivialTransformation :
    NonTrivialTransformationSem insight sourceFrame targetFrame

structure FinalityClaim (M : SigmaModel)
    (_claim : M.Carrier SortTag.claim) where
  finalForAllContexts : Prop
  noFurtherRevisionNeeded : Prop

def FinalityClaimSatisfied {M : SigmaModel}
    {claim : M.Carrier SortTag.claim}
    (finality : FinalityClaim M claim) : Prop :=
  And finality.finalForAllContexts finality.noFurtherRevisionNeeded

structure RepairClosureClaim (M : SigmaModel)
    (_claim : M.Carrier SortTag.claim) where
  repairComplete : Prop
  externalitiesResolved : Prop

def RepairClosureClaimSatisfied {M : SigmaModel}
    {claim : M.Carrier SortTag.claim}
    (repair : RepairClosureClaim M claim) : Prop :=
  And repair.repairComplete repair.externalitiesResolved

structure FalseInsightCase (M : SigmaModel) where
  insight : M.Carrier SortTag.candidateInsight
  candidate : CandidateInsightSem insight
  evaluatorRejected : Prop
  defectIdentified : Prop

structure NullInsightCase (M : SigmaModel) where
  frame : M.Carrier SortTag.frame
  context : M.Carrier SortTag.context
  claim : M.Carrier SortTag.claim
  contradictionPresent : ContradictionPresentSem frame context claim
  noCandidateGenerated : Prop

structure DeltaOutcomeCase (M : SigmaModel) where
  outcome : DeltaOutcome
  sourceFrame : M.Carrier SortTag.frame
  targetFrame : M.Carrier SortTag.frame
  claim : M.Carrier SortTag.claim
  transitionLicensed : Prop
  contradictionProcessed : Prop
  evaluatorClassified : Prop

structure DeltaOutcomeSatisfied {M : SigmaModel}
    (caseData : DeltaOutcomeCase M) : Prop where
  transitionLicensed : caseData.transitionLicensed
  contradictionProcessed : caseData.contradictionProcessed
  evaluatorClassified : caseData.evaluatorClassified

inductive DeltaPolicy where
  | exclusive
  | overlapAllowed
  deriving DecidableEq, Repr

def activeDeltaPolicy : DeltaPolicy := DeltaPolicy.exclusive

def DeltaOutcomesCompatible (policy : DeltaPolicy)
    (left right : DeltaOutcome) : Prop :=
  match policy with
  | DeltaPolicy.exclusive => left = right
  | DeltaPolicy.overlapAllowed => True

theorem exclusive_delta_compatibility_eq
    {left right : DeltaOutcome}
    (h : DeltaOutcomesCompatible DeltaPolicy.exclusive left right) :
    left = right :=
  h

theorem overlap_delta_compatibility_trivial
    (left right : DeltaOutcome) :
    DeltaOutcomesCompatible DeltaPolicy.overlapAllowed left right :=
  True.intro

def DeltaResolutionCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.resolution }

def DeltaShiftCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.shift }

def DeltaCollapseCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.collapse }

def DeltaIterativeCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.iterative }

def DeltaNullCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.null }

def DeltaFalseInsightCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.falseInsight }

def DeltaDegenerateCase (M : SigmaModel) : Type :=
  { d : DeltaOutcomeCase M // d.outcome = DeltaOutcome.degenerate }

def delta_case_compatible {M : SigmaModel}
    (policy : DeltaPolicy)
    (left right : DeltaOutcomeCase M) : Prop :=
  DeltaOutcomesCompatible policy left.outcome right.outcome

def DeltaOutcomeBlocked {M : SigmaModel}
    (caseData : DeltaOutcomeCase M) : Prop :=
  Or (Not caseData.transitionLicensed)
    (Or (Not caseData.contradictionProcessed)
      (Not caseData.evaluatorClassified))

theorem no_transition_blocks_delta {M : SigmaModel}
    (caseData : DeltaOutcomeCase M)
    (h : Not caseData.transitionLicensed) :
    DeltaOutcomeBlocked caseData :=
  Or.inl h

theorem unprocessed_contradiction_blocks_delta {M : SigmaModel}
    (caseData : DeltaOutcomeCase M)
    (h : Not caseData.contradictionProcessed) :
    DeltaOutcomeBlocked caseData :=
  Or.inr (Or.inl h)

theorem no_evaluator_classification_blocks_delta {M : SigmaModel}
    (caseData : DeltaOutcomeCase M)
    (h : Not caseData.evaluatorClassified) :
    DeltaOutcomeBlocked caseData :=
  Or.inr (Or.inr h)

def ValidInsightSem.toTransformableInsightCase {M : SigmaModel}
    {insight : M.Carrier SortTag.candidateInsight}
    {evaluator : M.Carrier SortTag.evaluator}
    {sourceFrame targetFrame : M.Carrier SortTag.frame}
    {claim : M.Carrier SortTag.claim}
    (h : ValidInsightSem M insight evaluator sourceFrame targetFrame claim) :
    TransformableInsightCase M :=
  { insight := insight
    sourceFrame := sourceFrame
    targetFrame := targetFrame
    candidate := h.candidateInsight
    licensedTransition := h.licensedTransition
    nonTrivialTransformation := h.nonTrivialTransformation }

theorem ValidInsightSem_addresses_contradiction {M : SigmaModel}
    {insight : M.Carrier SortTag.candidateInsight}
    {evaluator : M.Carrier SortTag.evaluator}
    {sourceFrame targetFrame : M.Carrier SortTag.frame}
    {claim : M.Carrier SortTag.claim}
    (h : ValidInsightSem M insight evaluator sourceFrame targetFrame claim) :
    ContradictionAddressedSem insight claim :=
  h.contradictionAddressed

def deltaResolutionOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.licensedTransition => True
  | PredicateSymbol.contradictionAddressed => True
  | PredicateSymbol.evaluatorAccepts => True
  | _ => False

def deltaResolutionOnlyModel : SigmaModel :=
  UnitPredicateModel deltaResolutionOnlyTruth

def deltaResolutionOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.resolution
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaResolutionOnlyCase :
    DeltaResolutionCase deltaResolutionOnlyModel :=
  ⟨deltaResolutionOnlyBaseCase, rfl⟩

theorem deltaResolutionOnly_satisfied :
    DeltaOutcomeSatisfied deltaResolutionOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

def deltaShiftOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.shift
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaCollapseOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.collapse
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaIterativeOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.iterative
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaNullOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.null
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaFalseInsightOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.falseInsight
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaDegenerateOnlyBaseCase :
    DeltaOutcomeCase deltaResolutionOnlyModel :=
  { outcome := DeltaOutcome.degenerate
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    claim := Unit.unit
    transitionLicensed := True
    contradictionProcessed := True
    evaluatorClassified := True }

def deltaShiftOnlyCase : DeltaShiftCase deltaResolutionOnlyModel :=
  ⟨deltaShiftOnlyBaseCase, rfl⟩

def deltaCollapseOnlyCase : DeltaCollapseCase deltaResolutionOnlyModel :=
  ⟨deltaCollapseOnlyBaseCase, rfl⟩

def deltaIterativeOnlyCase : DeltaIterativeCase deltaResolutionOnlyModel :=
  ⟨deltaIterativeOnlyBaseCase, rfl⟩

def deltaNullOnlyCase : DeltaNullCase deltaResolutionOnlyModel :=
  ⟨deltaNullOnlyBaseCase, rfl⟩

def deltaFalseInsightOnlyCase :
    DeltaFalseInsightCase deltaResolutionOnlyModel :=
  ⟨deltaFalseInsightOnlyBaseCase, rfl⟩

def deltaDegenerateOnlyCase : DeltaDegenerateCase deltaResolutionOnlyModel :=
  ⟨deltaDegenerateOnlyBaseCase, rfl⟩

theorem deltaShiftOnly_satisfied :
    DeltaOutcomeSatisfied deltaShiftOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem deltaCollapseOnly_satisfied :
    DeltaOutcomeSatisfied deltaCollapseOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem deltaIterativeOnly_satisfied :
    DeltaOutcomeSatisfied deltaIterativeOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem deltaNullOnly_satisfied :
    DeltaOutcomeSatisfied deltaNullOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem deltaFalseInsightOnly_satisfied :
    DeltaOutcomeSatisfied deltaFalseInsightOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem deltaDegenerateOnly_satisfied :
    DeltaOutcomeSatisfied deltaDegenerateOnlyBaseCase :=
  { transitionLicensed := True.intro
    contradictionProcessed := True.intro
    evaluatorClassified := True.intro }

theorem resolution_not_collapse_under_exclusive_policy :
    Not (DeltaOutcomesCompatible DeltaPolicy.exclusive DeltaOutcome.resolution
      DeltaOutcome.collapse) := by
  intro h
  cases h

theorem falseInsight_not_resolution_under_exclusive_policy :
    Not (DeltaOutcomesCompatible DeltaPolicy.exclusive
      DeltaOutcome.falseInsight DeltaOutcome.resolution) := by
  intro h
  cases h

theorem deltaShift_not_FullEmpiricalValidation :
    Not (FullEmpiricalValidationSem deltaResolutionOnlyModel Unit.unit
      Unit.unit) := by
  intro h
  exact h.validation

theorem deltaCollapse_not_MoralGuiltBridge :
    Not (MoralGuiltBridgeSem (M := deltaResolutionOnlyModel) Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem deltaIterative_not_RepairObligationBridge :
    Not (RepairObligationBridgeSem (M := deltaResolutionOnlyModel) Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h

theorem deltaDegenerate_not_HarmBridge :
    Not (HarmBridgeSem (M := deltaResolutionOnlyModel) Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem deltaResolution_not_FullEmpiricalValidation :
    Not (FullEmpiricalValidationSem deltaResolutionOnlyModel Unit.unit
      Unit.unit) := by
  intro h
  exact h.validation

theorem deltaResolution_not_HarmBridge :
    Not (HarmBridgeSem (M := deltaResolutionOnlyModel) Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem deltaResolution_not_RepairObligationBridge :
    Not (RepairObligationBridgeSem (M := deltaResolutionOnlyModel) Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h

def falseInsightOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.candidateInsight => True
  | _ => False

def falseInsightOnlyModel : SigmaModel :=
  UnitPredicateModel falseInsightOnlyTruth

def falseInsightOnlyCase : FalseInsightCase falseInsightOnlyModel :=
  { insight := Unit.unit
    candidate := True.intro
    evaluatorRejected := True
    defectIdentified := True }

theorem falseInsight_not_ValidInsightSem :
    Not (ValidInsightSem falseInsightOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.evaluatorAccepts

def nullInsightOnlyModel : SigmaModel :=
  contradictionOnlyModel

def nullInsightOnlyCase : NullInsightCase nullInsightOnlyModel :=
  { frame := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    contradictionPresent := True.intro
    noCandidateGenerated := True }

theorem nullInsight_not_ValidInsightSem :
    Not (ValidInsightSem nullInsightOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) :=
  contradictionOnly_not_ValidInsightSem

def validInsightOnlyFinalityClaim :
    FinalityClaim validInsightOnlyModel Unit.unit :=
  { finalForAllContexts := False
    noFurtherRevisionNeeded := False }

def validInsightOnlyRepairClosureClaim :
    RepairClosureClaim validInsightOnlyModel Unit.unit :=
  { repairComplete := False
    externalitiesResolved := False }

theorem validInsightOnly_not_finality :
    Not (FinalityClaimSatisfied validInsightOnlyFinalityClaim) := by
  intro h
  exact h.left

theorem validInsightOnly_not_repairClosure :
    Not (RepairClosureClaimSatisfied validInsightOnlyRepairClosureClaim) := by
  intro h
  exact h.left

def validInsightOnly_transformable :
    TransformableInsightCase validInsightOnlyModel :=
  ValidInsightSem.toTransformableInsightCase
    validInsightOnly_is_ValidInsightSem

theorem validInsightOnly_addresses_contradiction :
    ContradictionAddressedSem (M := validInsightOnlyModel) Unit.unit
      Unit.unit :=
  ValidInsightSem_addresses_contradiction validInsightOnly_is_ValidInsightSem

end Paralogic
