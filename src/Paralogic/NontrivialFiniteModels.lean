import Paralogic.FiniteModels

/-!
Nontrivial finite many-sorted models.

Most early semantic witnesses use one-element carriers.  This module adds a
two-element carrier for every sort and proves representative non-collapse
facts there, so the countermodel discipline is not limited to degenerate
one-object worlds.
-/

namespace Paralogic

def BoolCarrier (_ : SortTag) : Type := Bool

def boolFunctionInterp (f : FunctionSymbol)
    (_args : Args BoolCarrier ((functionArity f).domain)) :
    BoolCarrier ((functionArity f).codomain) :=
  false

def BoolPredicateModel (truth : PredicateSymbol -> Prop) : SigmaModel :=
  { Carrier := BoolCarrier
    interpFunction := boolFunctionInterp
    interpPredicate := fun p _args => truth p }

def boolFiniteSortWitness (truth : PredicateSymbol -> Prop)
    (s : SortTag) : FiniteSortWitness (BoolPredicateModel truth) s :=
  { elements := [false, true]
    covers := by
      intro x
      cases x
      · exact List.Mem.head [true]
      · exact List.Mem.tail false (List.Mem.head []) }

def boolFiniteModelWitness (truth : PredicateSymbol -> Prop) :
    FiniteModelWitness (BoolPredicateModel truth) :=
  { finiteCarrier := boolFiniteSortWitness truth }

theorem boolFiniteSortWitness_has_two_elements
    (truth : PredicateSymbol -> Prop) (s : SortTag) :
    ((boolFiniteSortWitness truth s).elements.length = 2) :=
  rfl

def twoUsesOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | _ => False

def twoUsesOnlyModel : SigmaModel :=
  BoolPredicateModel twoUsesOnlyTruth

theorem twoUsesOnly_has_UsesSem :
    UsesSem (M := twoUsesOnlyModel) true false :=
  True.intro

theorem twoUsesOnly_not_ISFSem :
    Not (ISFSem twoUsesOnlyModel true false true false true) := by
  intro h
  exact h.claims

def twoISFNotM8Truth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def twoISFNotM8Model : SigmaModel :=
  BoolPredicateModel twoISFNotM8Truth

theorem twoISFNotM8_is_ISFSem :
    ISFSem twoISFNotM8Model true false true false true :=
  { uses := True.intro
    claims := True.intro
    supportDegraded := True.intro
    treatsAsAdequate := True.intro }

theorem twoISFNotM8_not_M8Sem :
    Not (M8Sem twoISFNotM8Model true false true false true false true) := by
  intro h
  exact h.powerRelevant

end Paralogic
