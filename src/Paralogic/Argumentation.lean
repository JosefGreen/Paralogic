import Paralogic.Evaluator

/-!
Abstract argumentation layer.

This module gives evaluator reasoning a small Dung-style argumentation core:
arguments, attack, conflict-freeness, defense, and admissibility.  It proves a
finite counterexample showing that merely selecting an argument does not make
the selected set admissible.
-/

namespace Paralogic

structure ArgumentationFramework : Type 1 where
  Arg : Type
  attacks : Arg -> Arg -> Prop

def ConflictFree (framework : ArgumentationFramework)
    (selected : framework.Arg -> Prop) : Prop :=
  forall left right : framework.Arg,
    selected left ->
    selected right ->
      Not (framework.attacks left right)

def Defends (framework : ArgumentationFramework)
    (selected : framework.Arg -> Prop)
    (argument : framework.Arg) : Prop :=
  forall attacker : framework.Arg,
    framework.attacks attacker argument ->
      Exists (fun defender : framework.Arg =>
        And (selected defender) (framework.attacks defender attacker))

def Admissible (framework : ArgumentationFramework)
    (selected : framework.Arg -> Prop) : Prop :=
  And (ConflictFree framework selected)
    (forall argument : framework.Arg,
      selected argument -> Defends framework selected argument)

theorem admissible_is_conflict_free
    (framework : ArgumentationFramework)
    (selected : framework.Arg -> Prop)
    (h : Admissible framework selected) :
    ConflictFree framework selected :=
  h.left

theorem admissible_defends_selected
    (framework : ArgumentationFramework)
    (selected : framework.Arg -> Prop)
    (h : Admissible framework selected)
    {argument : framework.Arg}
    (hSelected : selected argument) :
    Defends framework selected argument :=
  h.right argument hSelected

inductive TwoArgument where
  | attacker
  | target
  deriving DecidableEq, Repr

def twoArgumentAttacks : TwoArgument -> TwoArgument -> Prop
  | TwoArgument.attacker, TwoArgument.target => True
  | _, _ => False

def twoArgumentFramework : ArgumentationFramework :=
  { Arg := TwoArgument
    attacks := twoArgumentAttacks }

def targetOnlySelection : TwoArgument -> Prop
  | TwoArgument.target => True
  | TwoArgument.attacker => False

theorem targetOnly_conflict_free :
    ConflictFree twoArgumentFramework targetOnlySelection := by
  intro left right hLeft hRight hAttack
  cases left <;> cases right <;> cases hLeft <;> cases hRight <;>
    cases hAttack

theorem targetOnly_not_defended :
    Not (Defends twoArgumentFramework targetOnlySelection
      TwoArgument.target) := by
  intro hDefends
  cases hDefends TwoArgument.attacker True.intro with
  | intro defender hDefender =>
      cases defender
      · exact hDefender.left
      · exact hDefender.right

theorem targetOnly_not_admissible :
    Not (Admissible twoArgumentFramework targetOnlySelection) := by
  intro hAdmissible
  exact targetOnly_not_defended
    (admissible_defends_selected twoArgumentFramework targetOnlySelection
      hAdmissible True.intro)

def emptySelection {framework : ArgumentationFramework} :
    framework.Arg -> Prop :=
  fun _ => False

theorem emptySelection_admissible
    (framework : ArgumentationFramework) :
    Admissible framework (emptySelection (framework := framework)) := by
  constructor
  · intro _ _ hSelected _ _
    exact hSelected
  · intro _ hSelected
    exact False.elim hSelected

end Paralogic
