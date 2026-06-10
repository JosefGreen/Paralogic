import Paralogic.Argumentation

/-!
Evaluator acceptance with argumentation defense.

This module connects the evaluator layer to the argumentation layer.  It
defines defended evaluator acceptance as evaluator acceptance plus
argumentation admissibility, then gives a checked counterexample where
evaluator acceptance exists but defended acceptance fails.
-/

namespace Paralogic

structure EvaluatorArgumentSelection (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  insight : M.Carrier SortTag.candidateInsight
  framework : ArgumentationFramework
  selected : framework.Arg -> Prop
  representedArgument : framework.Arg
  representedSelected : selected representedArgument
  evaluatorAccepts : EvaluatorAcceptsSem evaluator insight

def DefendedEvaluatorAcceptance {M : SigmaModel}
    (selection : EvaluatorArgumentSelection M) : Prop :=
  Admissible selection.framework selection.selected

theorem defended_acceptance_implies_evaluator_accepts {M : SigmaModel}
    (selection : EvaluatorArgumentSelection M)
    (_h : DefendedEvaluatorAcceptance selection) :
    EvaluatorAcceptsSem selection.evaluator selection.insight :=
  selection.evaluatorAccepts

theorem defended_acceptance_implies_admissible {M : SigmaModel}
    (selection : EvaluatorArgumentSelection M)
    (h : DefendedEvaluatorAcceptance selection) :
    Admissible selection.framework selection.selected :=
  h

def evaluatorAcceptedButUndefendedSelection :
    EvaluatorArgumentSelection evaluatorOnlyModel :=
  { evaluator := Unit.unit
    insight := Unit.unit
    framework := twoArgumentFramework
    selected := targetOnlySelection
    representedArgument := TwoArgument.target
    representedSelected := True.intro
    evaluatorAccepts := evaluatorOnly_accepts_sem }

theorem evaluatorAcceptedButUndefended_accepts :
    EvaluatorAcceptsSem
      evaluatorAcceptedButUndefendedSelection.evaluator
      evaluatorAcceptedButUndefendedSelection.insight :=
  evaluatorAcceptedButUndefendedSelection.evaluatorAccepts

theorem evaluator_acceptance_not_necessarily_defended :
    And
      (EvaluatorAcceptsSem
        evaluatorAcceptedButUndefendedSelection.evaluator
        evaluatorAcceptedButUndefendedSelection.insight)
      (Not (DefendedEvaluatorAcceptance
        evaluatorAcceptedButUndefendedSelection)) := by
  constructor
  · exact evaluatorAcceptedButUndefendedSelection.evaluatorAccepts
  · intro hDefended
    exact targetOnly_not_admissible hDefended

end Paralogic
