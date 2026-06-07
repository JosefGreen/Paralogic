/-!
Lean examples that serve as regression tests.

If any example fails, `lake build` fails.
-/

import Paralogic.Theorems

namespace Paralogic

example {w : World} (h : ISF w) : w.uses := ISF_to_Uses h
example {w : World} (h : ISF w) : w.claims := ISF_to_Claims h
example {w : World} (h : M8 w) : ISF w := M8_to_ISF h
example {w : World} (h : ValidInsight w) : w.evaluatorAccepts :=
  ValidInsight_to_EvaluatorAccepts h

example : usesOnlyWorld.uses ∧ ¬ ISF usesOnlyWorld :=
  ISF_does_not_follow_from_Uses

example : ISF isfNotM8World ∧ ¬ M8 isfNotM8World :=
  ISF_does_not_imply_M8

example : M8 m8NoBridgeWorld ∧ ¬ m8NoBridgeWorld.harm :=
  M8_does_not_imply_harm

example :
    ValidInsight validInsightNoBridgeWorld ∧
    ¬ validInsightNoBridgeWorld.empiricalTruth :=
  ValidInsight_does_not_imply_empiricalTruth

example :
    empiricalValidationNoLegitimacyWorld.empiricalValidation ∧
    ¬ empiricalValidationNoLegitimacyWorld.governanceLegitimacy :=
  EmpiricalValidation_does_not_imply_governanceLegitimacy

end Paralogic
