import Paralogic.Evaluator

/-!
Finite evaluator scoring, disagreement, and aggregation.

This module adds a small operational layer to the evaluator calculus.  It does
not validate any real evaluator empirically; it gives checked finite decision
procedures that separate scoring, threshold acceptance, disagreement, and
majority aggregation.
-/

namespace Paralogic

inductive ScoreLevel where
  | low
  | medium
  | high
  deriving DecidableEq, Repr

def scoreDecision : ScoreLevel -> EvaluationValue
  | ScoreLevel.low => EvaluationValue.rejects
  | ScoreLevel.medium => EvaluationValue.abstains
  | ScoreLevel.high => EvaluationValue.accepts

def ScoreAccepts (score : ScoreLevel) : Prop :=
  scoreDecision score = EvaluationValue.accepts

def ScoreRejects (score : ScoreLevel) : Prop :=
  scoreDecision score = EvaluationValue.rejects

def ScoreAbstains (score : ScoreLevel) : Prop :=
  scoreDecision score = EvaluationValue.abstains

theorem high_score_accepts :
    ScoreAccepts ScoreLevel.high := rfl

theorem medium_score_abstains :
    ScoreAbstains ScoreLevel.medium := rfl

theorem low_score_rejects :
    ScoreRejects ScoreLevel.low := rfl

theorem low_score_not_accepts :
    Not (ScoreAccepts ScoreLevel.low) := by
  intro h
  cases h

theorem medium_score_not_accepts :
    Not (ScoreAccepts ScoreLevel.medium) := by
  intro h
  cases h

def DecisionDisagreement
    (left right : EvaluationValue) : Prop :=
  Not (left = right)

theorem accepts_rejects_disagree :
    DecisionDisagreement EvaluationValue.accepts
      EvaluationValue.rejects := by
  intro h
  cases h

theorem accepts_abstains_disagree :
    DecisionDisagreement EvaluationValue.accepts
      EvaluationValue.abstains := by
  intro h
  cases h

def ScoreDisagreement
    (left right : ScoreLevel) : Prop :=
  DecisionDisagreement (scoreDecision left) (scoreDecision right)

theorem high_low_scores_disagree :
    ScoreDisagreement ScoreLevel.high ScoreLevel.low :=
  accepts_rejects_disagree

theorem high_medium_scores_disagree :
    ScoreDisagreement ScoreLevel.high ScoreLevel.medium :=
  accepts_abstains_disagree

structure ThreeEvaluatorScores where
  first : ScoreLevel
  second : ScoreLevel
  third : ScoreLevel

def AtLeastTwoAccept
    (scores : ThreeEvaluatorScores) : Prop :=
  Or (And (ScoreAccepts scores.first) (ScoreAccepts scores.second))
    (Or (And (ScoreAccepts scores.first) (ScoreAccepts scores.third))
      (And (ScoreAccepts scores.second) (ScoreAccepts scores.third)))

def majorityDecision (scores : ThreeEvaluatorScores) :
    EvaluationValue :=
  match scores.first, scores.second, scores.third with
  | ScoreLevel.high, ScoreLevel.high, _ => EvaluationValue.accepts
  | ScoreLevel.high, _, ScoreLevel.high => EvaluationValue.accepts
  | _, ScoreLevel.high, ScoreLevel.high => EvaluationValue.accepts
  | ScoreLevel.low, ScoreLevel.low, _ => EvaluationValue.rejects
  | ScoreLevel.low, _, ScoreLevel.low => EvaluationValue.rejects
  | _, ScoreLevel.low, ScoreLevel.low => EvaluationValue.rejects
  | _, _, _ => EvaluationValue.abstains

theorem two_high_one_low_majority_accepts :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.high
        third := ScoreLevel.low } = EvaluationValue.accepts := rfl

theorem one_high_two_low_majority_rejects :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.low
        third := ScoreLevel.low } = EvaluationValue.rejects := rfl

theorem one_high_two_medium_majority_abstains :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.medium
        third := ScoreLevel.medium } = EvaluationValue.abstains := rfl

theorem atLeastTwoAccept_two_high_one_low :
    AtLeastTwoAccept
      { first := ScoreLevel.high
        second := ScoreLevel.high
        third := ScoreLevel.low } :=
  Or.inl (And.intro rfl rfl)

theorem not_atLeastTwoAccept_one_high_two_medium :
    Not (AtLeastTwoAccept
      { first := ScoreLevel.high
        second := ScoreLevel.medium
        third := ScoreLevel.medium }) := by
  intro h
  cases h with
  | inl hPair =>
      exact medium_score_not_accepts hPair.right
  | inr hRest =>
      cases hRest with
      | inl hPair =>
          exact medium_score_not_accepts hPair.right
      | inr hPair =>
          exact medium_score_not_accepts hPair.left

end Paralogic
