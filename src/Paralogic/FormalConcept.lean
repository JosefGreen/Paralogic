/-!
Formal concept analysis fragment.

This module gives Paralogic a small checked vocabulary for category/evidence
formation: objects, attributes, an incidence relation, derivation operators,
and the Galois connection between object sets and attribute sets.
-/

namespace Paralogic

def PredicateSet (alpha : Type) : Type :=
  alpha -> Prop

def PredIncludes {alpha : Type}
    (left right : PredicateSet alpha) : Prop :=
  forall item : alpha, left item -> right item

def PredEquivalent {alpha : Type}
    (left right : PredicateSet alpha) : Prop :=
  forall item : alpha, Iff (left item) (right item)

theorem predEquivalent_symm {alpha : Type}
    {left right : PredicateSet alpha}
    (h : PredEquivalent left right) :
    PredEquivalent right left := by
  intro item
  exact (h item).symm

structure FormalContext : Type 1 where
  Obj : Type
  Attr : Type
  hasAttribute : Obj -> Attr -> Prop

def ExtentToIntent (context : FormalContext)
    (objects : PredicateSet context.Obj) :
    PredicateSet context.Attr :=
  fun attr =>
    forall obj : context.Obj, objects obj -> context.hasAttribute obj attr

def IntentToExtent (context : FormalContext)
    (attributes : PredicateSet context.Attr) :
    PredicateSet context.Obj :=
  fun obj =>
    forall attr : context.Attr, attributes attr -> context.hasAttribute obj attr

theorem formal_context_galois
    (context : FormalContext)
    (objects : PredicateSet context.Obj)
    (attributes : PredicateSet context.Attr) :
    Iff
      (PredIncludes objects (IntentToExtent context attributes))
      (PredIncludes attributes (ExtentToIntent context objects)) := by
  constructor
  · intro hObjects attr hAttr obj hObj
    exact hObjects obj hObj attr hAttr
  · intro hAttrs obj hObj attr hAttr
    exact hAttrs attr hAttr obj hObj

theorem extent_expands_under_double_derivation
    (context : FormalContext)
    (objects : PredicateSet context.Obj) :
    PredIncludes objects
      (IntentToExtent context (ExtentToIntent context objects)) := by
  intro obj hObj attr hAttr
  exact hAttr obj hObj

theorem intent_expands_under_double_derivation
    (context : FormalContext)
    (attributes : PredicateSet context.Attr) :
    PredIncludes attributes
      (ExtentToIntent context (IntentToExtent context attributes)) := by
  intro attr hAttr obj hObj
  exact hObj attr hAttr

structure FormalConcept (context : FormalContext) where
  extent : PredicateSet context.Obj
  intent : PredicateSet context.Attr
  extentClosed :
    PredEquivalent extent (IntentToExtent context intent)
  intentClosed :
    PredEquivalent intent (ExtentToIntent context extent)

inductive EvidenceObject where
  | recordA
  | recordB
  deriving DecidableEq, Repr

inductive EvidenceAttribute where
  | documented
  | contested
  deriving DecidableEq, Repr

def evidenceHasAttribute :
    EvidenceObject -> EvidenceAttribute -> Prop
  | EvidenceObject.recordA, EvidenceAttribute.documented => True
  | EvidenceObject.recordA, EvidenceAttribute.contested => False
  | EvidenceObject.recordB, EvidenceAttribute.documented => True
  | EvidenceObject.recordB, EvidenceAttribute.contested => True

def evidenceFormalContext : FormalContext :=
  { Obj := EvidenceObject
    Attr := EvidenceAttribute
    hasAttribute := evidenceHasAttribute }

def allEvidenceObjects : PredicateSet EvidenceObject :=
  fun _ => True

def documentedAttributeOnly :
    PredicateSet EvidenceAttribute :=
  fun attr => attr = EvidenceAttribute.documented

theorem allEvidence_intent_is_documented_only :
    PredEquivalent
      (ExtentToIntent evidenceFormalContext allEvidenceObjects)
      documentedAttributeOnly := by
  intro attr
  constructor
  · intro h
    cases attr
    · rfl
    · exact False.elim (h EvidenceObject.recordA True.intro)
  · intro hAttr obj _hObj
    cases hAttr
    cases obj <;> exact True.intro

theorem documented_only_extent_is_all_evidence :
    PredEquivalent
      (IntentToExtent evidenceFormalContext documentedAttributeOnly)
      allEvidenceObjects := by
  intro obj
  constructor
  · intro _h
    exact True.intro
  · intro _h attr hAttr
    cases hAttr
    cases obj <;> exact True.intro

def documentedEvidenceConcept :
    FormalConcept evidenceFormalContext :=
  { extent := allEvidenceObjects
    intent := documentedAttributeOnly
    extentClosed := predEquivalent_symm documented_only_extent_is_all_evidence
    intentClosed := predEquivalent_symm allEvidence_intent_is_documented_only }

theorem documentedEvidenceConcept_extent_contains_recordA :
    documentedEvidenceConcept.extent EvidenceObject.recordA :=
  True.intro

theorem documentedEvidenceConcept_intent_has_documented :
    documentedEvidenceConcept.intent EvidenceAttribute.documented :=
  rfl

theorem documentedEvidenceConcept_intent_not_contested :
    Not (documentedEvidenceConcept.intent EvidenceAttribute.contested) := by
  intro h
  cases h

end Paralogic
