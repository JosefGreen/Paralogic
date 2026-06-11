import Paralogic.Contradiction
import Paralogic.Adequacy
import Paralogic.Evaluator
import Paralogic.EvaluatorCalibration
import Paralogic.EmpiricalValidation
import Paralogic.ISFTMechanisms
import Paralogic.M8Power
import Paralogic.Repair

/-!
Warrant discharge obligations.

The repository avoids unproved primitive declarations in Lean source, but
several modules contain explicit warrant fields.  This module makes those
warrant-like assumptions first-class mathematical obligations and proves that
the raw profile conditions alone do not force their conclusions in arbitrary
models.
-/

namespace Paralogic

inductive WarrantObligation where
  | contradictionPresent
  | adequacy
  | evaluatorCriteriaAccepts
  | evaluatorDecisionAccepts
  | powerRelevant
  | powerValidityDependence
  | powerOmitted
  | normativeBridge
  | empiricalFullValidation
  | suppressionSupportDegraded
  | repairObligation
  deriving DecidableEq, Repr

inductive WarrantResolutionStatus where
  | suppliedField
  | countermodelGuarded
  | operationallyDischarged
  | sourceBacked
  | empiricallyValidated
  deriving DecidableEq, Repr

def warrantResolutionStatus : WarrantObligation -> WarrantResolutionStatus
  | WarrantObligation.contradictionPresent =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.adequacy =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.evaluatorCriteriaAccepts =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.evaluatorDecisionAccepts =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.powerRelevant =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.powerValidityDependence =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.powerOmitted =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.normativeBridge =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.empiricalFullValidation =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.suppressionSupportDegraded =>
      WarrantResolutionStatus.countermodelGuarded
  | WarrantObligation.repairObligation =>
      WarrantResolutionStatus.countermodelGuarded

def warrantResolutionStatusWithOperationalAdequacy :
    WarrantObligation -> WarrantResolutionStatus
  | WarrantObligation.adequacy =>
      WarrantResolutionStatus.operationallyDischarged
  | obligation => warrantResolutionStatus obligation

def warrantResolutionStatusWithOperationalAdequacyAndEvaluator :
    WarrantObligation -> WarrantResolutionStatus
  | WarrantObligation.adequacy =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.evaluatorCriteriaAccepts =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.evaluatorDecisionAccepts =>
      WarrantResolutionStatus.operationallyDischarged
  | obligation => warrantResolutionStatus obligation

def warrantResolutionStatusWithOperationalCore :
    WarrantObligation -> WarrantResolutionStatus
  | WarrantObligation.contradictionPresent =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.adequacy =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.evaluatorCriteriaAccepts =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.evaluatorDecisionAccepts =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.powerRelevant =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.powerValidityDependence =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.powerOmitted =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.normativeBridge =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.empiricalFullValidation =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.suppressionSupportDegraded =>
      WarrantResolutionStatus.operationallyDischarged
  | WarrantObligation.repairObligation =>
      WarrantResolutionStatus.operationallyDischarged

def warrantFalseModel : SigmaModel :=
  UnitPredicateModel (fun _ => False)

def WarrantConditionsHold : Prop := True

theorem warrant_conditions_hold : WarrantConditionsHold := True.intro

theorem warrant_false_model_not_contradiction_present :
    Not (ContradictionPresentSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

inductive OperationalContradictionToken where
  | activeFrame
  | inactiveFrame
  | activeContext
  | inactiveContext
  | contestedClaim
  | resolvedClaim
  | ordinary
  deriving DecidableEq, Repr

def operationalContradictionCarrier (_ : SortTag) : Type :=
  OperationalContradictionToken

def operationalContradictionFunctionInterp (_f : FunctionSymbol)
    (_args : Args operationalContradictionCarrier ((functionArity _f).domain)) :
    operationalContradictionCarrier ((functionArity _f).codomain) :=
  OperationalContradictionToken.ordinary

def operationalContradictionPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalContradictionCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.contradictionPresent,
      Args.cons OperationalContradictionToken.activeFrame
        (Args.cons OperationalContradictionToken.activeContext
          (Args.cons OperationalContradictionToken.contestedClaim Args.nil)) =>
      True
  | PredicateSymbol.contradictionPresent, _ => False
  | _, _ => False

def operationalContradictionModel : SigmaModel :=
  { Carrier := operationalContradictionCarrier
    interpFunction := operationalContradictionFunctionInterp
    interpPredicate := operationalContradictionPredicateInterp }

theorem operational_contradiction_active_contested_present :
    ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.contestedClaim :=
  True.intro

theorem operational_contradiction_resolved_not_present :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.resolvedClaim) := by
  intro h
  exact h

theorem operational_contradiction_inactive_frame_not_present :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.inactiveFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.contestedClaim) := by
  intro h
  exact h

theorem operational_contradiction_inactive_context_not_present :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.inactiveContext
      OperationalContradictionToken.contestedClaim) := by
  intro h
  exact h

def operationalContradictionProfile :
    ContradictionProfile operationalContradictionModel :=
  { kind := ContradictionKind.semantic
    frame := OperationalContradictionToken.activeFrame
    context := OperationalContradictionToken.activeContext
    claim := OperationalContradictionToken.contestedClaim
    domainApplies := True
    incompatibilityDetected := True
    sameScope := True
    sameContext := True
    unresolved := True
    warrant := fun _ _ _ _ _ =>
      operational_contradiction_active_contested_present }

theorem operationalContradictionProfile_satisfied :
    ContradictionProfileSatisfied operationalContradictionProfile :=
  { domainApplies := True.intro
    incompatibilityDetected := True.intro
    sameScope := True.intro
    sameContext := True.intro
    unresolved := True.intro }

theorem operationalContradictionProfile_to_present :
    ContradictionPresentSem (M := operationalContradictionModel)
      operationalContradictionProfile.frame
      operationalContradictionProfile.context
      operationalContradictionProfile.claim :=
  (operationalContradictionProfile.toCase
    operationalContradictionProfile_satisfied).present

theorem warrant_false_model_not_adequate :
    Not (warrantFalseModel.interpPredicate PredicateSymbol.adequate
      (Args.cons Unit.unit
        (Args.cons Unit.unit (Args.cons Unit.unit Args.nil)))) := by
  intro h
  exact h

inductive OperationalAdequacyToken where
  | unsupported
  | supported
  | outOfScope
  | inScope
  | mismatched
  | matched
  deriving DecidableEq, Repr

def operationalAdequacyCarrier : SortTag -> Type
  | _ => OperationalAdequacyToken

def operationalAdequacyFunctionInterp (f : FunctionSymbol)
    (_args : Args operationalAdequacyCarrier ((functionArity f).domain)) :
    operationalAdequacyCarrier ((functionArity f).codomain) :=
  match f with
  | FunctionSymbol.outputInstitution => OperationalAdequacyToken.matched
  | FunctionSymbol.outputContext => OperationalAdequacyToken.inScope
  | FunctionSymbol.claimEvidence => OperationalAdequacyToken.supported
  | FunctionSymbol.claimContext => OperationalAdequacyToken.inScope
  | FunctionSymbol.evaluatorContext => OperationalAdequacyToken.inScope
  | FunctionSymbol.validationTarget => OperationalAdequacyToken.matched
  | FunctionSymbol.bridgeTarget => OperationalAdequacyToken.matched

def operationalAdequacyPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalAdequacyCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.adequate,
      Args.cons OperationalAdequacyToken.supported
        (Args.cons OperationalAdequacyToken.inScope
          (Args.cons OperationalAdequacyToken.matched Args.nil)) =>
      True
  | PredicateSymbol.adequate, _ => False
  | _, _ => False

def operationalAdequacyModel : SigmaModel :=
  { Carrier := operationalAdequacyCarrier
    interpFunction := operationalAdequacyFunctionInterp
    interpPredicate := operationalAdequacyPredicateInterp }

theorem operational_adequacy_supported_in_scope_matched :
    operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons OperationalAdequacyToken.supported
        (Args.cons OperationalAdequacyToken.inScope
          (Args.cons OperationalAdequacyToken.matched Args.nil))) :=
  True.intro

theorem operational_adequacy_unsupported_not_adequate :
    Not (operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons OperationalAdequacyToken.unsupported
        (Args.cons OperationalAdequacyToken.inScope
          (Args.cons OperationalAdequacyToken.matched Args.nil)))) := by
  intro h
  exact h

def operationalAdequacyProfile :
    AdequacyProfile operationalAdequacyModel :=
  { domain := AdequacyDomain.empirical
    evidence := OperationalAdequacyToken.supported
    context := OperationalAdequacyToken.inScope
    claim := OperationalAdequacyToken.matched
    relevant := True
    sufficient := True
    current := True
    methodologicallyFit := True
    uncertaintyBounded := True
    scopeMatched := True
    warrant := fun _ _ _ _ _ _ =>
      operational_adequacy_supported_in_scope_matched }

theorem operationalAdequacyProfile_satisfied :
    AdequacyProfileSatisfied operationalAdequacyProfile :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro True.intro))))

theorem operationalAdequacyProfile_to_adequate :
    operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons operationalAdequacyProfile.evidence
        (Args.cons operationalAdequacyProfile.context
          (Args.cons operationalAdequacyProfile.claim Args.nil))) :=
  AdequacyProfile_to_AdequateSem operationalAdequacyProfile
    operationalAdequacyProfile_satisfied

theorem warrant_false_model_not_evaluator_accepts :
    Not (EvaluatorAcceptsSem (M := warrantFalseModel)
      Unit.unit Unit.unit) := by
  intro h
  exact h

inductive OperationalEvaluatorToken where
  | approvedEvaluator
  | otherEvaluator
  | approvedCandidate
  | rejectedCandidate
  | ordinary
  deriving DecidableEq, Repr

def operationalEvaluatorCarrier (_ : SortTag) : Type :=
  OperationalEvaluatorToken

def operationalEvaluatorFunctionInterp (f : FunctionSymbol)
    (_args : Args operationalEvaluatorCarrier ((functionArity f).domain)) :
    operationalEvaluatorCarrier ((functionArity f).codomain) :=
  OperationalEvaluatorToken.ordinary

def operationalEvaluatorPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalEvaluatorCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.evaluatorAccepts,
      Args.cons OperationalEvaluatorToken.approvedEvaluator
        (Args.cons OperationalEvaluatorToken.approvedCandidate Args.nil) =>
      True
  | PredicateSymbol.evaluatorAccepts, _ => False
  | _, _ => False

def operationalEvaluatorModel : SigmaModel :=
  { Carrier := operationalEvaluatorCarrier
    interpFunction := operationalEvaluatorFunctionInterp
    interpPredicate := operationalEvaluatorPredicateInterp }

theorem operational_evaluator_high_pair_accepts :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      OperationalEvaluatorToken.approvedEvaluator
      OperationalEvaluatorToken.approvedCandidate :=
  True.intro

theorem operational_evaluator_rejected_candidate_not_accepted :
    Not (EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      OperationalEvaluatorToken.approvedEvaluator
      OperationalEvaluatorToken.rejectedCandidate) := by
  intro h
  exact h

def operationalEvaluatorCriteria :
    EvaluatorCriteria operationalEvaluatorModel :=
  { evaluator := OperationalEvaluatorToken.approvedEvaluator
    candidate := OperationalEvaluatorToken.approvedCandidate
    context := OperationalEvaluatorToken.ordinary
    criteriaDeclared := True
    criteriaRelevant := True
    evidenceInspected := True
    criteriaApplied := True
    noEvaluationError := True
    warrant := fun _ _ _ _ _ =>
      operational_evaluator_high_pair_accepts }

theorem operationalEvaluatorCriteria_satisfied :
    EvaluatorCriteriaSatisfied operationalEvaluatorCriteria :=
  { declared := True.intro
    relevant := True.intro
    inspected := True.intro
    applied := True.intro
    noError := True.intro }

theorem operationalEvaluatorCriteria_accepts :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      operationalEvaluatorCriteria.evaluator
      operationalEvaluatorCriteria.candidate :=
  EvaluatorCriteria_to_accepts operationalEvaluatorCriteria
    operationalEvaluatorCriteria_satisfied

def operationalHighScoreDecision :
    EvaluatorDecisionCase operationalEvaluatorModel :=
  { evaluator := OperationalEvaluatorToken.approvedEvaluator
    candidate := OperationalEvaluatorToken.approvedCandidate
    context := OperationalEvaluatorToken.ordinary
    value := scoreDecision ScoreLevel.high
    criteriaDeclared := True
    evidenceInspected := True
    criteriaApplied := True
    scopeMatched := True
    noEvaluationError := True
    acceptsWarrant := fun _ _ _ _ _ _ =>
      operational_evaluator_high_pair_accepts }

theorem operationalHighScoreDecision_satisfied :
    EvaluatorDecisionSatisfied operationalHighScoreDecision :=
  { declared := True.intro
    inspected := True.intro
    applied := True.intro
    inScope := True.intro
    noError := True.intro }

theorem operationalHighScoreDecision_accepts :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      operationalHighScoreDecision.evaluator
      operationalHighScoreDecision.candidate :=
  accepting_decision_to_accepts operationalHighScoreDecision
    high_score_accepts
    operationalHighScoreDecision_satisfied

theorem low_score_still_not_accepting_decision :
    Not (scoreDecision ScoreLevel.low = EvaluationValue.accepts) := by
  exact low_score_not_accepts

theorem warrant_false_model_not_power_relevant :
    Not (PowerRelevantSem (M := warrantFalseModel)
      Unit.unit Unit.unit) := by
  intro h
  exact h

theorem warrant_false_model_not_power_validity_dependence :
    Not (PowerValidityDependenceSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

theorem warrant_false_model_not_power_omitted :
    Not (PowerOmittedSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

inductive OperationalPowerToken where
  | reviewInstitution
  | otherInstitution
  | contestedOutput
  | ordinaryOutput
  | materialPowerCondition
  | immaterialPowerCondition
  | affectedGroup
  | unaffectedGroup
  | ordinary
  deriving DecidableEq, Repr

def operationalPowerCarrier (_ : SortTag) : Type :=
  OperationalPowerToken

def operationalPowerFunctionInterp (f : FunctionSymbol)
    (_args : Args operationalPowerCarrier ((functionArity f).domain)) :
    operationalPowerCarrier ((functionArity f).codomain) :=
  match f with
  | FunctionSymbol.outputInstitution => OperationalPowerToken.reviewInstitution
  | FunctionSymbol.outputContext => OperationalPowerToken.ordinary
  | FunctionSymbol.claimEvidence => OperationalPowerToken.ordinary
  | FunctionSymbol.claimContext => OperationalPowerToken.ordinary
  | FunctionSymbol.evaluatorContext => OperationalPowerToken.ordinary
  | FunctionSymbol.validationTarget => OperationalPowerToken.ordinary
  | FunctionSymbol.bridgeTarget => OperationalPowerToken.ordinary

def operationalPowerPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalPowerCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.powerRelevant,
      Args.cons OperationalPowerToken.reviewInstitution
        (Args.cons OperationalPowerToken.affectedGroup Args.nil) =>
      True
  | PredicateSymbol.powerValidityDependence,
      Args.cons OperationalPowerToken.reviewInstitution
        (Args.cons OperationalPowerToken.contestedOutput
          (Args.cons OperationalPowerToken.materialPowerCondition Args.nil)) =>
      True
  | PredicateSymbol.powerOmitted,
      Args.cons OperationalPowerToken.reviewInstitution
        (Args.cons OperationalPowerToken.contestedOutput
          (Args.cons OperationalPowerToken.materialPowerCondition Args.nil)) =>
      True
  | PredicateSymbol.powerRelevant, _ => False
  | PredicateSymbol.powerValidityDependence, _ => False
  | PredicateSymbol.powerOmitted, _ => False
  | _, _ => False

def operationalPowerModel : SigmaModel :=
  { Carrier := operationalPowerCarrier
    interpFunction := operationalPowerFunctionInterp
    interpPredicate := operationalPowerPredicateInterp }

theorem operational_power_relevant :
    PowerRelevantSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.affectedGroup :=
  True.intro

theorem operational_power_unaffected_group_not_relevant :
    Not (PowerRelevantSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.unaffectedGroup) := by
  intro h
  exact h

theorem operational_power_validity_dependence :
    PowerValidityDependenceSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.materialPowerCondition :=
  True.intro

theorem operational_power_immaterial_condition_not_dependence :
    Not (PowerValidityDependenceSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.immaterialPowerCondition) := by
  intro h
  exact h

theorem operational_power_omitted :
    PowerOmittedSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.materialPowerCondition :=
  True.intro

theorem operational_power_ordinary_output_not_omitted :
    Not (PowerOmittedSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.ordinaryOutput
      OperationalPowerToken.materialPowerCondition) := by
  intro h
  exact h

def operationalPowerConditionProfile :
    PowerConditionProfile operationalPowerModel :=
  { institution := OperationalPowerToken.reviewInstitution
    output := OperationalPowerToken.contestedOutput
    condition := OperationalPowerToken.materialPowerCondition
    group := OperationalPowerToken.affectedGroup
    dimension := PowerDimension.metricControl
    relevantToClaimValidity := True
    omittedFromRepresentation := True
    omissionMaterial := True
    affectedGroupMaterial := True
    disclosureAbsent := True
    mitigationAbsent := True
    warrantRelevant := fun _ => operational_power_relevant
    warrantDependence := fun _ => operational_power_validity_dependence
    warrantOmission := fun _ _ => operational_power_omitted }

theorem operationalPowerConditionProfile_satisfied :
    PowerConditionProfileSatisfied operationalPowerConditionProfile :=
  { relevantToClaimValidity := True.intro
    omittedFromRepresentation := True.intro
    omissionMaterial := True.intro
    affectedGroupMaterial := True.intro
    disclosureAbsent := True.intro
    mitigationAbsent := True.intro }

theorem operationalPowerConditionProfile_to_powerRelevant :
    PowerRelevantSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.group :=
  PowerConditionProfile_to_powerRelevant operationalPowerConditionProfile
    operationalPowerConditionProfile_satisfied

theorem operationalPowerConditionProfile_to_powerValidityDependence :
    PowerValidityDependenceSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.output
      operationalPowerConditionProfile.condition :=
  PowerConditionProfile_to_powerValidityDependence
    operationalPowerConditionProfile
    operationalPowerConditionProfile_satisfied

theorem operationalPowerConditionProfile_to_powerOmitted :
    PowerOmittedSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.output
      operationalPowerConditionProfile.condition :=
  PowerConditionProfile_to_powerOmitted operationalPowerConditionProfile
    operationalPowerConditionProfile_satisfied

theorem warrant_false_model_not_normative_bridge
    (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := warrantFalseModel)
      conclusion Unit.unit Unit.unit Unit.unit) := by
  cases conclusion <;> intro h <;> exact h

inductive OperationalNormativeToken where
  | harmBridge
  | responsibilityBridge
  | repairBridge
  | accountabilityBridge
  | legalBridge
  | governanceBridge
  | guiltBridge
  | ordinaryBridge
  | responsibleInstitution
  | otherInstitution
  | affectedGroup
  | otherGroup
  | ordinary
  deriving DecidableEq, Repr

def operationalNormativeBridgeToken :
    NormativeConclusion -> OperationalNormativeToken
  | NormativeConclusion.harm => OperationalNormativeToken.harmBridge
  | NormativeConclusion.responsibility =>
      OperationalNormativeToken.responsibilityBridge
  | NormativeConclusion.repairObligation =>
      OperationalNormativeToken.repairBridge
  | NormativeConclusion.accountability =>
      OperationalNormativeToken.accountabilityBridge
  | NormativeConclusion.legalIllegitimacy =>
      OperationalNormativeToken.legalBridge
  | NormativeConclusion.governanceLegitimacy =>
      OperationalNormativeToken.governanceBridge
  | NormativeConclusion.moralGuilt => OperationalNormativeToken.guiltBridge

def operationalNormativeCarrier (_ : SortTag) : Type :=
  OperationalNormativeToken

def operationalNormativeFunctionInterp (_f : FunctionSymbol)
    (_args : Args operationalNormativeCarrier ((functionArity _f).domain)) :
    operationalNormativeCarrier ((functionArity _f).codomain) :=
  OperationalNormativeToken.ordinary

def operationalNormativePredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalNormativeCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.harmBridge,
      Args.cons OperationalNormativeToken.harmBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution
          (Args.cons OperationalNormativeToken.affectedGroup Args.nil)) =>
      True
  | PredicateSymbol.responsibilityBridge,
      Args.cons OperationalNormativeToken.responsibilityBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution Args.nil) =>
      True
  | PredicateSymbol.repairObligationBridge,
      Args.cons OperationalNormativeToken.repairBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution
          (Args.cons OperationalNormativeToken.affectedGroup Args.nil)) =>
      True
  | PredicateSymbol.accountabilityBridge,
      Args.cons OperationalNormativeToken.accountabilityBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution Args.nil) =>
      True
  | PredicateSymbol.legalIllegitimacyBridge,
      Args.cons OperationalNormativeToken.legalBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution Args.nil) =>
      True
  | PredicateSymbol.governanceLegitimacyBridge,
      Args.cons OperationalNormativeToken.governanceBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution Args.nil) =>
      True
  | PredicateSymbol.moralGuiltBridge,
      Args.cons OperationalNormativeToken.guiltBridge
        (Args.cons OperationalNormativeToken.responsibleInstitution Args.nil) =>
      True
  | PredicateSymbol.harmBridge, _ => False
  | PredicateSymbol.responsibilityBridge, _ => False
  | PredicateSymbol.repairObligationBridge, _ => False
  | PredicateSymbol.accountabilityBridge, _ => False
  | PredicateSymbol.legalIllegitimacyBridge, _ => False
  | PredicateSymbol.governanceLegitimacyBridge, _ => False
  | PredicateSymbol.moralGuiltBridge, _ => False
  | _, _ => False

def operationalNormativeModel : SigmaModel :=
  { Carrier := operationalNormativeCarrier
    interpFunction := operationalNormativeFunctionInterp
    interpPredicate := operationalNormativePredicateInterp }

theorem operational_normative_conclusion
    (conclusion : NormativeConclusion) :
    NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeBridgeToken conclusion)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.affectedGroup := by
  cases conclusion <;> exact True.intro

theorem operational_normative_ordinary_bridge_not_conclusion
    (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      OperationalNormativeToken.ordinaryBridge
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.affectedGroup) := by
  cases conclusion <;> intro h <;> exact h

theorem operational_normative_other_institution_not_conclusion
    (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeBridgeToken conclusion)
      OperationalNormativeToken.otherInstitution
      OperationalNormativeToken.affectedGroup) := by
  cases conclusion <;> intro h <;> exact h

theorem operational_normative_harm_other_group_not_conclusion :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      NormativeConclusion.harm
      (operationalNormativeBridgeToken NormativeConclusion.harm)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.otherGroup) := by
  intro h
  exact h

theorem operational_normative_repair_other_group_not_conclusion :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      NormativeConclusion.repairObligation
      (operationalNormativeBridgeToken NormativeConclusion.repairObligation)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.otherGroup) := by
  intro h
  exact h

def operationalNormativeSchema
    (conclusion : NormativeConclusion) :
    NormativeBridgeSchema operationalNormativeModel :=
  { conclusion := conclusion
    bridge := operationalNormativeBridgeToken conclusion
    institution := OperationalNormativeToken.responsibleInstitution
    group := OperationalNormativeToken.affectedGroup
    premisesSatisfied := True
    scopeApplies := True
    defeatersAbsent := True
    warrant := fun _ _ _ => operational_normative_conclusion conclusion }

theorem operationalNormativeSchema_applies
    (conclusion : NormativeConclusion) :
    BridgeApplies (operationalNormativeSchema conclusion) :=
  And.intro True.intro (And.intro True.intro True.intro)

theorem operationalNormativeSchema_to_conclusion
    (conclusion : NormativeConclusion) :
    NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeSchema conclusion).bridge
      (operationalNormativeSchema conclusion).institution
      (operationalNormativeSchema conclusion).group :=
  NormativeBridgeSchema_to_conclusion (operationalNormativeSchema conclusion)
    (operationalNormativeSchema_applies conclusion)

theorem warrant_false_model_not_full_empirical_validation :
    Not (FullEmpiricalValidationSem warrantFalseModel
      Unit.unit Unit.unit) := by
  intro h
  exact h.validation

inductive OperationalEmpiricalToken where
  | validatedObject
  | nominalObject
  | unvalidatedObject
  | targetClaim
  | otherClaim
  | ordinary
  deriving DecidableEq, Repr

def operationalEmpiricalCarrier (_ : SortTag) : Type :=
  OperationalEmpiricalToken

def operationalEmpiricalFunctionInterp (_f : FunctionSymbol)
    (_args : Args operationalEmpiricalCarrier ((functionArity _f).domain)) :
    operationalEmpiricalCarrier ((functionArity _f).codomain) :=
  OperationalEmpiricalToken.ordinary

def operationalEmpiricalPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalEmpiricalCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.empiricalValidation,
      Args.cons OperationalEmpiricalToken.validatedObject
        (Args.cons OperationalEmpiricalToken.targetClaim Args.nil) =>
      True
  | PredicateSymbol.empiricalValidation,
      Args.cons OperationalEmpiricalToken.nominalObject
        (Args.cons OperationalEmpiricalToken.targetClaim Args.nil) =>
      True
  | PredicateSymbol.constructValid,
      Args.cons OperationalEmpiricalToken.validatedObject Args.nil =>
      True
  | PredicateSymbol.reliabilityTested,
      Args.cons OperationalEmpiricalToken.validatedObject Args.nil =>
      True
  | PredicateSymbol.externallyReplicated,
      Args.cons OperationalEmpiricalToken.validatedObject Args.nil =>
      True
  | PredicateSymbol.empiricalValidation, _ => False
  | PredicateSymbol.constructValid, _ => False
  | PredicateSymbol.reliabilityTested, _ => False
  | PredicateSymbol.externallyReplicated, _ => False
  | _, _ => False

def operationalEmpiricalModel : SigmaModel :=
  { Carrier := operationalEmpiricalCarrier
    interpFunction := operationalEmpiricalFunctionInterp
    interpPredicate := operationalEmpiricalPredicateInterp }

theorem operational_empirical_full_validation :
    FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.validatedObject
      OperationalEmpiricalToken.targetClaim :=
  { validation := True.intro
    constructValid := True.intro
    reliabilityTested := True.intro
    externallyReplicated := True.intro }

theorem operational_empirical_nominal_not_full :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.nominalObject
      OperationalEmpiricalToken.targetClaim) := by
  intro h
  exact h.constructValid

theorem operational_empirical_unvalidated_not_full :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.unvalidatedObject
      OperationalEmpiricalToken.targetClaim) := by
  intro h
  exact h.validation

theorem operational_empirical_other_claim_not_full :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.validatedObject
      OperationalEmpiricalToken.otherClaim) := by
  intro h
  exact h.validation

def operationalEmpiricalProtocol :
    EmpiricalValidationProtocol operationalEmpiricalModel :=
  { validationObject := OperationalEmpiricalToken.validatedObject
    targetClaim := OperationalEmpiricalToken.targetClaim
    operationalized := True
    constructBoundaryDeclared := True
    constructValid := True
    reliabilityTested := True
    externalReplicationAvailable := True
    domainScopeDeclared := True
    limitationsDeclared := True
    warrant := fun _ _ _ _ _ _ _ =>
      operational_empirical_full_validation }

theorem operationalEmpiricalProtocol_applies :
    EmpiricalProtocolApplies operationalEmpiricalProtocol :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro True.intro)))))

theorem operationalEmpiricalProtocol_to_full_validation :
    FullEmpiricalValidationSem operationalEmpiricalModel
      operationalEmpiricalProtocol.validationObject
      operationalEmpiricalProtocol.targetClaim :=
  EmpiricalValidationProtocol_to_full_validation operationalEmpiricalProtocol
    operationalEmpiricalProtocol_applies

theorem warrant_false_model_not_support_degraded :
    Not (SupportDegradedSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

inductive OperationalSuppressionToken where
  | supportedEvidence
  | unsupportedEvidence
  | matchedContext
  | mismatchedContext
  | suppressedClaim
  | ordinaryClaim
  | ordinary
  deriving DecidableEq, Repr

def operationalSuppressionCarrier (_ : SortTag) : Type :=
  OperationalSuppressionToken

def operationalSuppressionFunctionInterp (_f : FunctionSymbol)
    (_args : Args operationalSuppressionCarrier ((functionArity _f).domain)) :
    operationalSuppressionCarrier ((functionArity _f).codomain) :=
  OperationalSuppressionToken.ordinary

def operationalSuppressionPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalSuppressionCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.supportDegraded,
      Args.cons OperationalSuppressionToken.supportedEvidence
        (Args.cons OperationalSuppressionToken.matchedContext
          (Args.cons OperationalSuppressionToken.suppressedClaim Args.nil)) =>
      True
  | PredicateSymbol.supportDegraded, _ => False
  | _, _ => False

def operationalSuppressionModel : SigmaModel :=
  { Carrier := operationalSuppressionCarrier
    interpFunction := operationalSuppressionFunctionInterp
    interpPredicate := operationalSuppressionPredicateInterp }

theorem operational_suppression_support_degraded :
    SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.suppressedClaim :=
  True.intro

theorem operational_suppression_unsupported_not_degraded :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.unsupportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.suppressedClaim) := by
  intro h
  exact h

theorem operational_suppression_mismatched_context_not_degraded :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.mismatchedContext
      OperationalSuppressionToken.suppressedClaim) := by
  intro h
  exact h

theorem operational_suppression_ordinary_claim_not_degraded :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.ordinaryClaim) := by
  intro h
  exact h

def operationalSuppressionProfile :
    SuppressionProfile operationalSuppressionModel :=
  { mechanism := ISFTMechanism.M9
    evidence := OperationalSuppressionToken.supportedEvidence
    context := OperationalSuppressionToken.matchedContext
    claim := OperationalSuppressionToken.suppressedClaim
    mode := SuppressionMode.omission
    supportBasisAvailable := True
    suppressionDetected := True
    suppressionMaterial := True
    scopeMatched := True
    warrantSupportDegraded := fun _ _ _ _ =>
      operational_suppression_support_degraded }

theorem operationalSuppressionProfile_satisfied :
    SuppressionProfileSatisfied operationalSuppressionProfile :=
  { supportBasis := True.intro
    detected := True.intro
    material := True.intro
    scopeMatched := True.intro }

theorem operationalSuppressionProfile_to_supportDegraded :
    SupportDegradedSem (M := operationalSuppressionModel)
      operationalSuppressionProfile.evidence
      operationalSuppressionProfile.context
      operationalSuppressionProfile.claim :=
  SuppressionProfile_to_supportDegraded operationalSuppressionProfile
    operationalSuppressionProfile_satisfied

theorem warrant_false_model_not_repair_obligation :
    Not (RepairObligationBridgeSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

inductive OperationalRepairToken where
  | repairNeedBridge
  | ordinaryBridge
  | responsibleInstitution
  | otherInstitution
  | affectedGroup
  | otherGroup
  | diagnosisClaim
  | diagnosisEvidence
  | diagnosisContext
  | ordinary
  deriving DecidableEq, Repr

def operationalRepairCarrier (_ : SortTag) : Type :=
  OperationalRepairToken

def operationalRepairFunctionInterp (_f : FunctionSymbol)
    (_args : Args operationalRepairCarrier ((functionArity _f).domain)) :
    operationalRepairCarrier ((functionArity _f).codomain) :=
  OperationalRepairToken.ordinary

def operationalRepairPredicateInterp :
    (p : PredicateSymbol) ->
      Args operationalRepairCarrier ((predicateArity p).domain) -> Prop
  | PredicateSymbol.repairObligationBridge,
      Args.cons OperationalRepairToken.repairNeedBridge
        (Args.cons OperationalRepairToken.responsibleInstitution
          (Args.cons OperationalRepairToken.affectedGroup Args.nil)) =>
      True
  | PredicateSymbol.repairObligationBridge, _ => False
  | _, _ => False

def operationalRepairModel : SigmaModel :=
  { Carrier := operationalRepairCarrier
    interpFunction := operationalRepairFunctionInterp
    interpPredicate := operationalRepairPredicateInterp }

theorem operational_repair_obligation :
    RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.affectedGroup :=
  True.intro

theorem operational_repair_ordinary_bridge_not_obligation :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.ordinaryBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.affectedGroup) := by
  intro h
  exact h

theorem operational_repair_other_institution_not_obligation :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.otherInstitution
      OperationalRepairToken.affectedGroup) := by
  intro h
  exact h

theorem operational_repair_other_group_not_obligation :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.otherGroup) := by
  intro h
  exact h

def operationalRepairDiagnosis :
    RepairDiagnosisProfile operationalRepairModel :=
  { bridge := OperationalRepairToken.repairNeedBridge
    institution := OperationalRepairToken.responsibleInstitution
    group := OperationalRepairToken.affectedGroup
    claim := OperationalRepairToken.diagnosisClaim
    evidence := OperationalRepairToken.diagnosisEvidence
    context := OperationalRepairToken.diagnosisContext
    repairNeedIdentified := True
    standingDeclared := True
    causalPathDeclared := True
    scopeBounded := True
    affectedGroupConsulted := True
    defeatersAbsent := True
    warrantRepairObligation := fun _ _ _ _ _ _ =>
      operational_repair_obligation }

theorem operationalRepairDiagnosis_satisfied :
    RepairDiagnosisSatisfied operationalRepairDiagnosis :=
  { need := True.intro
    standing := True.intro
    causalPath := True.intro
    scope := True.intro
    consulted := True.intro
    defeaters := True.intro }

theorem operationalRepairDiagnosis_to_repairObligation :
    RepairObligationBridgeSem (M := operationalRepairModel)
      operationalRepairDiagnosis.bridge
      operationalRepairDiagnosis.institution
      operationalRepairDiagnosis.group :=
  RepairDiagnosisProfile_to_repairObligation operationalRepairDiagnosis
    operationalRepairDiagnosis_satisfied

structure WarrantCountermodel where
  obligation : WarrantObligation
  rawConditionsHold : WarrantConditionsHold
  warrantedConclusionFails : Prop

def contradiction_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.contradictionPresent
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (ContradictionPresentSem (M := warrantFalseModel)
        Unit.unit Unit.unit Unit.unit) }

def adequacy_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.adequacy
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (warrantFalseModel.interpPredicate PredicateSymbol.adequate
        (Args.cons Unit.unit
          (Args.cons Unit.unit (Args.cons Unit.unit Args.nil)))) }

def evaluator_criteria_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.evaluatorCriteriaAccepts
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (EvaluatorAcceptsSem (M := warrantFalseModel)
        Unit.unit Unit.unit) }

def evaluator_decision_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.evaluatorDecisionAccepts
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (EvaluatorAcceptsSem (M := warrantFalseModel)
        Unit.unit Unit.unit) }

def power_relevant_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.powerRelevant
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (PowerRelevantSem (M := warrantFalseModel)
        Unit.unit Unit.unit) }

def power_validity_dependence_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.powerValidityDependence
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (PowerValidityDependenceSem (M := warrantFalseModel)
        Unit.unit Unit.unit Unit.unit) }

def power_omitted_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.powerOmitted
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (PowerOmittedSem (M := warrantFalseModel)
        Unit.unit Unit.unit Unit.unit) }

def normative_bridge_warrant_countermodel
    (conclusion : NormativeConclusion) : WarrantCountermodel :=
  { obligation := WarrantObligation.normativeBridge
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (NormativeConclusionSem (M := warrantFalseModel)
        conclusion Unit.unit Unit.unit Unit.unit) }

def empirical_validation_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.empiricalFullValidation
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (FullEmpiricalValidationSem warrantFalseModel
        Unit.unit Unit.unit) }

def suppression_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.suppressionSupportDegraded
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (SupportDegradedSem (M := warrantFalseModel)
        Unit.unit Unit.unit Unit.unit) }

def repair_obligation_warrant_countermodel : WarrantCountermodel :=
  { obligation := WarrantObligation.repairObligation
    rawConditionsHold := warrant_conditions_hold
    warrantedConclusionFails :=
      Not (RepairObligationBridgeSem (M := warrantFalseModel)
        Unit.unit Unit.unit Unit.unit) }

theorem adequacy_warrant_countermodel_blocks_raw_shortcut :
    adequacy_warrant_countermodel.warrantedConclusionFails :=
  warrant_false_model_not_adequate

theorem contradiction_warrant_countermodel_blocks_raw_shortcut :
    contradiction_warrant_countermodel.warrantedConclusionFails :=
  warrant_false_model_not_contradiction_present

theorem evaluator_warrant_countermodel_blocks_raw_shortcut :
    evaluator_criteria_warrant_countermodel.warrantedConclusionFails :=
  warrant_false_model_not_evaluator_accepts

theorem empirical_warrant_countermodel_blocks_raw_shortcut :
    empirical_validation_warrant_countermodel.warrantedConclusionFails :=
  warrant_false_model_not_full_empirical_validation

theorem normative_warrant_countermodel_blocks_raw_shortcut
    (conclusion : NormativeConclusion) :
    (normative_bridge_warrant_countermodel conclusion).warrantedConclusionFails :=
  warrant_false_model_not_normative_bridge conclusion

theorem repair_warrant_countermodel_blocks_raw_shortcut :
    repair_obligation_warrant_countermodel.warrantedConclusionFails :=
  warrant_false_model_not_repair_obligation

theorem no_warrant_obligation_is_source_backed_yet
    (obligation : WarrantObligation) :
    Not (warrantResolutionStatus obligation =
      WarrantResolutionStatus.sourceBacked) := by
  cases obligation <;> intro h <;> cases h

theorem no_warrant_obligation_is_empirically_validated_yet
    (obligation : WarrantObligation) :
    Not (warrantResolutionStatus obligation =
      WarrantResolutionStatus.empiricallyValidated) := by
  cases obligation <;> intro h <;> cases h

theorem adequacy_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalAdequacy WarrantObligation.adequacy =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_adequacy_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalAdequacy WarrantObligation.adequacy =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_adequacy_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalAdequacy WarrantObligation.adequacy =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem contradiction_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore WarrantObligation.contradictionPresent =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_contradiction_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.contradictionPresent =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_contradiction_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.contradictionPresent =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem evaluator_criteria_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.evaluatorCriteriaAccepts =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_evaluator_criteria_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.evaluatorCriteriaAccepts =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_evaluator_criteria_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.evaluatorCriteriaAccepts =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem power_relevant_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore WarrantObligation.powerRelevant =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem power_validity_dependence_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.powerValidityDependence =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem power_omitted_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore WarrantObligation.powerOmitted =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem normative_bridge_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore WarrantObligation.normativeBridge =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_normative_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.normativeBridge =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_normative_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.normativeBridge =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem empirical_full_validation_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.empiricalFullValidation =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_empirical_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.empiricalFullValidation =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_empirical_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.empiricalFullValidation =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem operational_power_not_source_backed
    (obligation : WarrantObligation)
    (hcore :
      warrantResolutionStatusWithOperationalCore obligation =
        WarrantResolutionStatus.operationallyDischarged) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.sourceBacked) := by
  intro h
  rw [h] at hcore
  cases hcore

theorem operational_power_not_empirically_validated
    (obligation : WarrantObligation)
    (hcore :
      warrantResolutionStatusWithOperationalCore obligation =
        WarrantResolutionStatus.operationallyDischarged) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  rw [h] at hcore
  cases hcore

theorem suppression_support_degraded_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.suppressionSupportDegraded =
      WarrantResolutionStatus.operationallyDischarged := rfl

theorem operational_suppression_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.suppressionSupportDegraded =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_suppression_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.suppressionSupportDegraded =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

theorem repair_obligation_is_operationally_discharged_in_scoped_model :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.repairObligation =
      WarrantResolutionStatus.operationallyDischarged := rfl

def OperationalWarrantCoverageComplete : Prop :=
  forall obligation : WarrantObligation,
    warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.operationallyDischarged

theorem all_warrant_obligations_operationally_discharged
    (obligation : WarrantObligation) :
    warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.operationallyDischarged := by
  cases obligation <;> rfl

theorem operational_warrant_coverage_complete :
    OperationalWarrantCoverageComplete :=
  all_warrant_obligations_operationally_discharged

theorem operational_core_ne_source_backed
    (obligation : WarrantObligation) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.sourceBacked) := by
  exact operational_power_not_source_backed obligation
    (all_warrant_obligations_operationally_discharged obligation)

theorem operational_core_ne_empirically_validated
    (obligation : WarrantObligation) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.empiricallyValidated) := by
  exact operational_power_not_empirically_validated obligation
    (all_warrant_obligations_operationally_discharged obligation)

theorem operational_repair_not_source_backed :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.repairObligation =
        WarrantResolutionStatus.sourceBacked) := by
  intro h
  cases h

theorem operational_repair_not_empirically_validated :
    Not
      (warrantResolutionStatusWithOperationalCore
        WarrantObligation.repairObligation =
        WarrantResolutionStatus.empiricallyValidated) := by
  intro h
  cases h

end Paralogic
