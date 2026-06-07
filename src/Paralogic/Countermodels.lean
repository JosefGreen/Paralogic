/-!
Executable finite countermodel witnesses.

Every theorem here is a witness that a tempting implication fails. These are
not sociological, moral, legal, or empirical findings; they are finite semantic
models inside the one-object kernel.
-/

import Paralogic.ISFT
import Paralogic.Insight

namespace Paralogic

def usesOnlyWorld : World := { emptyWorld with uses := True }

theorem usesOnly_has_uses : usesOnlyWorld.uses := True.intro

theorem usesOnly_not_ISF : ¬ ISF usesOnlyWorld := by
  intro h
  exact h.claims

def claimsOnlyWorld : World := { emptyWorld with claims := True }

theorem claimsOnly_has_claims : claimsOnlyWorld.claims := True.intro

theorem claimsOnly_not_ISF : ¬ ISF claimsOnlyWorld := by
  intro h
  exact h.uses

def supportOnlyWorld : World := { emptyWorld with supportDegraded := True }

theorem supportOnly_has_supportDegraded : supportOnlyWorld.supportDegraded :=
  True.intro

theorem supportOnly_not_ISF : ¬ ISF supportOnlyWorld := by
  intro h
  exact h.uses

def noTreatmentWorld : World :=
  { emptyWorld with
    uses := True
    claims := True
    supportDegraded := True }

theorem noTreatment_not_ISF : ¬ ISF noTreatmentWorld := by
  intro h
  exact h.treatsAsAdequate

def isfNotM8World : World :=
  { emptyWorld with
    uses := True
    claims := True
    supportDegraded := True
    treatsAsAdequate := True }

theorem isfNotM8_is_ISF : ISF isfNotM8World :=
  { uses := True.intro
    claims := True.intro
    supportDegraded := True.intro
    treatsAsAdequate := True.intro }

theorem isfNotM8_not_M8 : ¬ M8 isfNotM8World := by
  intro h
  exact h.powerRelevant

def m8NoBridgeWorld : World :=
  { emptyWorld with
    uses := True
    claims := True
    supportDegraded := True
    treatsAsAdequate := True
    powerRelevant := True
    powerValidityDependence := True
    powerOmitted := True }

theorem m8NoBridge_is_M8 : M8 m8NoBridgeWorld :=
  { uses := True.intro
    claims := True.intro
    powerRelevant := True.intro
    powerValidityDependence := True.intro
    powerOmitted := True.intro
    supportDegraded := True.intro
    treatsAsAdequate := True.intro }

theorem m8_not_discrimination : ¬ m8NoBridgeWorld.discrimination := by
  intro h
  exact h

theorem m8_not_coercion : ¬ m8NoBridgeWorld.coercion := by
  intro h
  exact h

theorem m8_not_harm : ¬ m8NoBridgeWorld.harm := by
  intro h
  exact h

theorem m8_not_illegality : ¬ m8NoBridgeWorld.illegality := by
  intro h
  exact h

theorem m8_not_moralGuilt : ¬ m8NoBridgeWorld.moralGuilt := by
  intro h
  exact h

theorem m8_not_repairObligation : ¬ m8NoBridgeWorld.repairObligation := by
  intro h
  exact h

def evaluatorOnlyWorld : World := { emptyWorld with evaluatorAccepts := True }

theorem evaluatorOnly_accepts : evaluatorOnlyWorld.evaluatorAccepts := True.intro

theorem evaluatorOnly_not_ValidInsight : ¬ ValidInsight evaluatorOnlyWorld := by
  intro h
  exact h.candidateInsight

def validInsightNoBridgeWorld : World :=
  { emptyWorld with
    candidateInsight := True
    evaluatorAccepts := True
    licensedTransition := True
    nonTrivialTransformation := True
    contradictionAddressed := True
    noHigherOrderDefeater := True
    generativityMinimal := True
    directionalNonEquivalence := True }

theorem validInsightNoBridge_is_ValidInsight :
    ValidInsight validInsightNoBridgeWorld :=
  { candidateInsight := True.intro
    evaluatorAccepts := True.intro
    licensedTransition := True.intro
    nonTrivialTransformation := True.intro
    contradictionAddressed := True.intro
    noHigherOrderDefeater := True.intro
    generativityMinimal := True.intro
    directionalNonEquivalence := True.intro }

theorem validInsight_not_empiricalTruth :
    ¬ validInsightNoBridgeWorld.empiricalTruth := by
  intro h
  exact h

theorem validInsight_not_moralTruth :
    ¬ validInsightNoBridgeWorld.moralTruth := by
  intro h
  exact h

theorem validInsight_not_repair :
    ¬ validInsightNoBridgeWorld.repair := by
  intro h
  exact h

def deltaResolutionNoTruthWorld : World :=
  { emptyWorld with deltaResolution := True }

theorem deltaResolution_not_empiricalTruth :
    ¬ deltaResolutionNoTruthWorld.empiricalTruth := by
  intro h
  exact h

def empiricalValidationNoLegitimacyWorld : World :=
  { emptyWorld with empiricalValidation := True }

theorem empiricalValidation_not_governanceLegitimacy :
    ¬ empiricalValidationNoLegitimacyWorld.governanceLegitimacy := by
  intro h
  exact h

end Paralogic
