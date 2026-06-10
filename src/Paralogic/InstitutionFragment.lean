/-!
Institution-style local logic fragments.

This module starts the institution-theoretic lane with a compact local-logic
interface: sentences, models, satisfaction, translations, reducts, and the
satisfaction condition.  It also gives a finite counterexample showing that a
mere syntactic translation/reduct pair need not preserve satisfaction.
-/

namespace Paralogic

structure LogicFragment : Type 1 where
  Sentence : Type
  Model : Type
  satisfies : Model -> Sentence -> Prop

structure FragmentTranslation
    (source target : LogicFragment) : Type 1 where
  translateSentence : source.Sentence -> target.Sentence
  reductModel : target.Model -> source.Model

def SatisfactionCondition
    {source target : LogicFragment}
    (translation : FragmentTranslation source target) : Prop :=
  forall (model : target.Model) (sentence : source.Sentence),
    Iff
      (target.satisfies model (translation.translateSentence sentence))
      (source.satisfies (translation.reductModel model) sentence)

theorem satisfaction_condition_forward
    {source target : LogicFragment}
    (translation : FragmentTranslation source target)
    (hCondition : SatisfactionCondition translation)
    (model : target.Model)
    (sentence : source.Sentence)
    (hTarget :
      target.satisfies model (translation.translateSentence sentence)) :
    source.satisfies (translation.reductModel model) sentence :=
  (hCondition model sentence).mp hTarget

theorem satisfaction_condition_backward
    {source target : LogicFragment}
    (translation : FragmentTranslation source target)
    (hCondition : SatisfactionCondition translation)
    (model : target.Model)
    (sentence : source.Sentence)
    (hSource :
      source.satisfies (translation.reductModel model) sentence) :
    target.satisfies model (translation.translateSentence sentence) :=
  (hCondition model sentence).mpr hSource

def alwaysTrueFragment : LogicFragment :=
  { Sentence := Unit
    Model := Unit
    satisfies := fun _ _ => True }

def alwaysFalseFragment : LogicFragment :=
  { Sentence := Unit
    Model := Unit
    satisfies := fun _ _ => False }

def unitSyntaxTranslation :
    FragmentTranslation alwaysTrueFragment alwaysFalseFragment :=
  { translateSentence := fun _ => Unit.unit
    reductModel := fun _ => Unit.unit }

theorem unitSyntaxTranslation_not_satisfaction_preserving :
    Not (SatisfactionCondition unitSyntaxTranslation) := by
  intro hCondition
  exact (hCondition Unit.unit Unit.unit).mpr True.intro

def identityFragmentTranslation
    (fragment : LogicFragment) :
    FragmentTranslation fragment fragment :=
  { translateSentence := fun sentence => sentence
    reductModel := fun model => model }

theorem identityFragmentTranslation_satisfies_condition
    (fragment : LogicFragment) :
    SatisfactionCondition (identityFragmentTranslation fragment) := by
  intro _ _
  exact Iff.rfl

end Paralogic
