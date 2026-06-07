/-!
Finite semantic kernel.

`World` is a one-object finite abstraction: each primitive predicate is a
proposition. Defined predicates in other modules are conjunctions over these
primitive fields. This model is deliberately modest, but it is enough to prove
core implications and non-entailments inside Lean.
-/

import Paralogic.CoreTypes

namespace Paralogic

structure World where
  uses : Prop
  claims : Prop
  supportDegraded : Prop
  treatsAsAdequate : Prop
  powerRelevant : Prop
  powerValidityDependence : Prop
  powerOmitted : Prop
  candidateInsight : Prop
  evaluatorAccepts : Prop
  licensedTransition : Prop
  nonTrivialTransformation : Prop
  contradictionAddressed : Prop
  noHigherOrderDefeater : Prop
  generativityMinimal : Prop
  directionalNonEquivalence : Prop
  frameShift : Prop
  deltaResolution : Prop
  empiricalTruth : Prop
  moralTruth : Prop
  repair : Prop
  discrimination : Prop
  coercion : Prop
  harm : Prop
  illegality : Prop
  moralGuilt : Prop
  repairObligation : Prop
  governanceLegitimacy : Prop
  accountability : Prop
  empiricalValidation : Prop

def emptyWorld : World :=
  { uses := False
    claims := False
    supportDegraded := False
    treatsAsAdequate := False
    powerRelevant := False
    powerValidityDependence := False
    powerOmitted := False
    candidateInsight := False
    evaluatorAccepts := False
    licensedTransition := False
    nonTrivialTransformation := False
    contradictionAddressed := False
    noHigherOrderDefeater := False
    generativityMinimal := False
    directionalNonEquivalence := False
    frameShift := False
    deltaResolution := False
    empiricalTruth := False
    moralTruth := False
    repair := False
    discrimination := False
    coercion := False
    harm := False
    illegality := False
    moralGuilt := False
    repairObligation := False
    governanceLegitimacy := False
    accountability := False
    empiricalValidation := False }

inductive PredicateName where
  | uses
  | claims
  | supportDegraded
  | treatsAsAdequate
  | powerRelevant
  | powerValidityDependence
  | powerOmitted
  | candidateInsight
  | evaluatorAccepts
  | empiricalTruth
  | moralTruth
  | repair
  | harm
  deriving DecidableEq, Repr

def supportsPredicate (w : World) (name : PredicateName) : Prop :=
  match name with
  | PredicateName.uses => w.uses
  | PredicateName.claims => w.claims
  | PredicateName.supportDegraded => w.supportDegraded
  | PredicateName.treatsAsAdequate => w.treatsAsAdequate
  | PredicateName.powerRelevant => w.powerRelevant
  | PredicateName.powerValidityDependence => w.powerValidityDependence
  | PredicateName.powerOmitted => w.powerOmitted
  | PredicateName.candidateInsight => w.candidateInsight
  | PredicateName.evaluatorAccepts => w.evaluatorAccepts
  | PredicateName.empiricalTruth => w.empiricalTruth
  | PredicateName.moralTruth => w.moralTruth
  | PredicateName.repair => w.repair
  | PredicateName.harm => w.harm

def Satisfies (w : World) (p : World -> Prop) : Prop := p w

theorem empty_world_not_uses : ¬ emptyWorld.uses := by
  intro h
  exact h

end Paralogic
