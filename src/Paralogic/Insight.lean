/-!
Evaluator-gated insight fragment.
-/

import Paralogic.Semantics

namespace Paralogic

structure ValidInsight (w : World) : Prop where
  candidateInsight : w.candidateInsight
  evaluatorAccepts : w.evaluatorAccepts
  licensedTransition : w.licensedTransition
  nonTrivialTransformation : w.nonTrivialTransformation
  contradictionAddressed : w.contradictionAddressed
  noHigherOrderDefeater : w.noHigherOrderDefeater
  generativityMinimal : w.generativityMinimal
  directionalNonEquivalence : w.directionalNonEquivalence

theorem ValidInsight_to_CandidateInsight {w : World} (h : ValidInsight w) :
    w.candidateInsight := h.candidateInsight

theorem ValidInsight_to_EvaluatorAccepts {w : World} (h : ValidInsight w) :
    w.evaluatorAccepts := h.evaluatorAccepts

theorem ValidInsight_to_LicensedTransition {w : World} (h : ValidInsight w) :
    w.licensedTransition := h.licensedTransition

theorem ValidInsight_to_ContradictionAddressed {w : World} (h : ValidInsight w) :
    w.contradictionAddressed := h.contradictionAddressed

end Paralogic
