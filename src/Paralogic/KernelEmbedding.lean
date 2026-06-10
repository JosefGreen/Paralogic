import Paralogic.Semantics
import Paralogic.ISFT
import Paralogic.Insight
import Paralogic.Countermodels
import Paralogic.ModelSemantics

/-!
Embedding of the one-object `World` kernel into the many-sorted semantics.

This module connects the early finite kernel to the later `SigmaModel` layer.
The embedding uses unit carriers for every sort and interprets the relevant
many-sorted predicates by the corresponding fields of `World`.
-/

namespace Paralogic

def worldPredicateTruth (w : World) : PredicateSymbol -> Prop
  | PredicateSymbol.uses => w.uses
  | PredicateSymbol.claims => w.claims
  | PredicateSymbol.supportDegraded => w.supportDegraded
  | PredicateSymbol.treatsAsAdequate => w.treatsAsAdequate
  | PredicateSymbol.powerRelevant => w.powerRelevant
  | PredicateSymbol.powerValidityDependence => w.powerValidityDependence
  | PredicateSymbol.powerOmitted => w.powerOmitted
  | PredicateSymbol.candidateInsight => w.candidateInsight
  | PredicateSymbol.evaluatorAccepts => w.evaluatorAccepts
  | PredicateSymbol.licensedTransition => w.licensedTransition
  | PredicateSymbol.nonTrivialTransformation => w.nonTrivialTransformation
  | PredicateSymbol.contradictionAddressed => w.contradictionAddressed
  | PredicateSymbol.noHigherOrderDefeater => w.noHigherOrderDefeater
  | PredicateSymbol.generativityMinimal => w.generativityMinimal
  | PredicateSymbol.directionalNonEquivalence => w.directionalNonEquivalence
  | PredicateSymbol.empiricalValidation => w.empiricalValidation
  | PredicateSymbol.harmBridge => w.harm
  | PredicateSymbol.legalIllegitimacyBridge => w.illegality
  | PredicateSymbol.governanceLegitimacyBridge => w.governanceLegitimacy
  | PredicateSymbol.moralGuiltBridge => w.moralGuilt
  | PredicateSymbol.repairObligationBridge => w.repairObligation
  | PredicateSymbol.accountabilityBridge => w.accountability
  | _ => False

def WorldSigmaModel (w : World) : SigmaModel :=
  UnitPredicateModel (worldPredicateTruth w)

theorem world_uses_iff_UsesSem (w : World) :
    Iff w.uses
      (UsesSem (M := WorldSigmaModel w) Unit.unit Unit.unit) :=
  Iff.rfl

theorem world_claims_iff_ClaimsSem (w : World) :
    Iff w.claims
      (ClaimsSem (M := WorldSigmaModel w) Unit.unit Unit.unit Unit.unit) :=
  Iff.rfl

theorem world_supportDegraded_iff_SupportDegradedSem (w : World) :
    Iff w.supportDegraded
      (SupportDegradedSem (M := WorldSigmaModel w) Unit.unit Unit.unit
        Unit.unit) :=
  Iff.rfl

theorem world_treatsAsAdequate_iff_TreatsAsAdequateSem (w : World) :
    Iff w.treatsAsAdequate
      (TreatsAsAdequateSem (M := WorldSigmaModel w) Unit.unit Unit.unit
        Unit.unit Unit.unit) :=
  Iff.rfl

theorem world_ISF_to_ISFSem {w : World} (h : ISF w) :
    ISFSem (WorldSigmaModel w) Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  { uses := h.uses
    claims := h.claims
    supportDegraded := h.supportDegraded
    treatsAsAdequate := h.treatsAsAdequate }

theorem world_M8_to_M8Sem {w : World} (h : M8 w) :
    M8Sem (WorldSigmaModel w) Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit Unit.unit :=
  { uses := h.uses
    claims := h.claims
    powerRelevant := h.powerRelevant
    powerValidityDependence := h.powerValidityDependence
    powerOmitted := h.powerOmitted
    supportDegraded := h.supportDegraded
    treatsAsAdequate := h.treatsAsAdequate }

theorem world_ValidInsight_to_ValidInsightSem {w : World}
    (h : ValidInsight w) :
    ValidInsightSem (WorldSigmaModel w) Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  { candidateInsight := h.candidateInsight
    evaluatorAccepts := h.evaluatorAccepts
    licensedTransition := h.licensedTransition
    nonTrivialTransformation := h.nonTrivialTransformation
    contradictionAddressed := h.contradictionAddressed
    noHigherOrderDefeater := h.noHigherOrderDefeater
    generativityMinimal := h.generativityMinimal
    directionalNonEquivalence := h.directionalNonEquivalence }

theorem world_m8NoBridge_not_HarmBridgeSem :
    Not (HarmBridgeSem (M := WorldSigmaModel m8NoBridgeWorld)
      Unit.unit Unit.unit Unit.unit) :=
  m8_not_harm

theorem world_m8NoBridge_not_MoralGuiltBridgeSem :
    Not (MoralGuiltBridgeSem (M := WorldSigmaModel m8NoBridgeWorld)
      Unit.unit Unit.unit) :=
  m8_not_moralGuilt

theorem world_m8NoBridge_not_RepairObligationBridgeSem :
    Not (RepairObligationBridgeSem (M := WorldSigmaModel m8NoBridgeWorld)
      Unit.unit Unit.unit Unit.unit) :=
  m8_not_repairObligation

theorem world_evaluatorOnly_not_ValidInsightSem :
    Not (ValidInsightSem (WorldSigmaModel evaluatorOnlyWorld) Unit.unit
      Unit.unit Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact evaluatorOnly_not_ValidInsight
    { candidateInsight := h.candidateInsight
      evaluatorAccepts := h.evaluatorAccepts
      licensedTransition := h.licensedTransition
      nonTrivialTransformation := h.nonTrivialTransformation
      contradictionAddressed := h.contradictionAddressed
      noHigherOrderDefeater := h.noHigherOrderDefeater
      generativityMinimal := h.generativityMinimal
      directionalNonEquivalence := h.directionalNonEquivalence }

theorem world_validInsightNoBridge_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem
      (WorldSigmaModel validInsightNoBridgeWorld) Unit.unit Unit.unit) := by
  intro h
  exact validInsight_not_empiricalTruth h.validation

end Paralogic
