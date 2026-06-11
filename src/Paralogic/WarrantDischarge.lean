import Paralogic.Contradiction
import Paralogic.Adequacy
import Paralogic.Evaluator
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

def warrantFalseModel : SigmaModel :=
  UnitPredicateModel (fun _ => False)

def WarrantConditionsHold : Prop := True

theorem warrant_conditions_hold : WarrantConditionsHold := True.intro

theorem warrant_false_model_not_contradiction_present :
    Not (ContradictionPresentSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

theorem warrant_false_model_not_adequate :
    Not (warrantFalseModel.interpPredicate PredicateSymbol.adequate
      (Args.cons Unit.unit
        (Args.cons Unit.unit (Args.cons Unit.unit Args.nil)))) := by
  intro h
  exact h

theorem warrant_false_model_not_evaluator_accepts :
    Not (EvaluatorAcceptsSem (M := warrantFalseModel)
      Unit.unit Unit.unit) := by
  intro h
  exact h

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

theorem warrant_false_model_not_normative_bridge
    (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := warrantFalseModel)
      conclusion Unit.unit Unit.unit Unit.unit) := by
  cases conclusion <;> intro h <;> exact h

theorem warrant_false_model_not_full_empirical_validation :
    Not (FullEmpiricalValidationSem warrantFalseModel
      Unit.unit Unit.unit) := by
  intro h
  exact h.validation

theorem warrant_false_model_not_support_degraded :
    Not (SupportDegradedSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

theorem warrant_false_model_not_repair_obligation :
    Not (RepairObligationBridgeSem (M := warrantFalseModel)
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

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

end Paralogic
