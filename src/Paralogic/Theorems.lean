/-!
Core theorem ledger encoded in Lean.
-/

import Paralogic.Countermodels

namespace Paralogic

theorem ISF_does_not_follow_from_Uses :
    usesOnlyWorld.uses ∧ ¬ ISF usesOnlyWorld :=
  ⟨usesOnly_has_uses, usesOnly_not_ISF⟩

theorem ISF_does_not_follow_from_Claims :
    claimsOnlyWorld.claims ∧ ¬ ISF claimsOnlyWorld :=
  ⟨claimsOnly_has_claims, claimsOnly_not_ISF⟩

theorem ISF_does_not_follow_from_SupportDegraded :
    supportOnlyWorld.supportDegraded ∧ ¬ ISF supportOnlyWorld :=
  ⟨supportOnly_has_supportDegraded, supportOnly_not_ISF⟩

theorem ISF_needs_TreatsAsAdequate :
    noTreatmentWorld.uses ∧
    noTreatmentWorld.claims ∧
    noTreatmentWorld.supportDegraded ∧
    ¬ ISF noTreatmentWorld :=
  ⟨True.intro, True.intro, True.intro, noTreatment_not_ISF⟩

theorem ISF_does_not_imply_M8 :
    ISF isfNotM8World ∧ ¬ M8 isfNotM8World :=
  ⟨isfNotM8_is_ISF, isfNotM8_not_M8⟩

theorem M8_does_not_imply_harm :
    M8 m8NoBridgeWorld ∧ ¬ m8NoBridgeWorld.harm :=
  ⟨m8NoBridge_is_M8, m8_not_harm⟩

theorem M8_does_not_imply_illegality :
    M8 m8NoBridgeWorld ∧ ¬ m8NoBridgeWorld.illegality :=
  ⟨m8NoBridge_is_M8, m8_not_illegality⟩

theorem M8_does_not_imply_moralGuilt :
    M8 m8NoBridgeWorld ∧ ¬ m8NoBridgeWorld.moralGuilt :=
  ⟨m8NoBridge_is_M8, m8_not_moralGuilt⟩

theorem EvaluatorAccepts_does_not_imply_ValidInsight :
    evaluatorOnlyWorld.evaluatorAccepts ∧ ¬ ValidInsight evaluatorOnlyWorld :=
  ⟨evaluatorOnly_accepts, evaluatorOnly_not_ValidInsight⟩

theorem ValidInsight_does_not_imply_empiricalTruth :
    ValidInsight validInsightNoBridgeWorld ∧
    ¬ validInsightNoBridgeWorld.empiricalTruth :=
  ⟨validInsightNoBridge_is_ValidInsight, validInsight_not_empiricalTruth⟩

theorem ValidInsight_does_not_imply_repair :
    ValidInsight validInsightNoBridgeWorld ∧
    ¬ validInsightNoBridgeWorld.repair :=
  ⟨validInsightNoBridge_is_ValidInsight, validInsight_not_repair⟩

theorem DeltaResolution_does_not_imply_empiricalTruth :
    deltaResolutionNoTruthWorld.deltaResolution ∧
    ¬ deltaResolutionNoTruthWorld.empiricalTruth :=
  ⟨True.intro, deltaResolution_not_empiricalTruth⟩

theorem EmpiricalValidation_does_not_imply_governanceLegitimacy :
    empiricalValidationNoLegitimacyWorld.empiricalValidation ∧
    ¬ empiricalValidationNoLegitimacyWorld.governanceLegitimacy :=
  ⟨True.intro, empiricalValidation_not_governanceLegitimacy⟩

end Paralogic
