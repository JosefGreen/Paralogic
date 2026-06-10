import Paralogic.FormalConcept
import Paralogic.ISFTMechanisms

/-!
Concept-based category essentialization blockers.

This module adds a narrow, checked bridge from formal concept analysis to the
M7 "Category Essentialization" label.  It does not claim to complete M7
semantics.  It only proves that a category-attribution profile is blocked when
the attributed feature is not in the formal concept's intent.
-/

namespace Paralogic

structure ConceptAttributionProfile (context : FormalContext) where
  concept : FormalConcept context
  obj : context.Obj
  attr : context.Attr
  mechanism : ISFTMechanism
  objectInExtent : concept.extent obj
  attributeInIntent : Prop
  intentWarrant : attributeInIntent -> concept.intent attr

def ConceptAttributionSatisfied {context : FormalContext}
    (profile : ConceptAttributionProfile context) : Prop :=
  And (profile.mechanism = ISFTMechanism.M7)
    profile.attributeInIntent

def ConceptAttributionBlocked {context : FormalContext}
    (profile : ConceptAttributionProfile context) : Prop :=
  Or (Not (profile.mechanism = ISFTMechanism.M7))
    (Not profile.attributeInIntent)

theorem non_M7_blocks_concept_attribution {context : FormalContext}
    (profile : ConceptAttributionProfile context)
    (h : Not (profile.mechanism = ISFTMechanism.M7)) :
    ConceptAttributionBlocked profile :=
  Or.inl h

theorem missing_intent_blocks_concept_attribution {context : FormalContext}
    (profile : ConceptAttributionProfile context)
    (h : Not profile.attributeInIntent) :
    ConceptAttributionBlocked profile :=
  Or.inr h

theorem concept_attribution_satisfied_intent {context : FormalContext}
    (profile : ConceptAttributionProfile context)
    (h : ConceptAttributionSatisfied profile) :
    profile.concept.intent profile.attr :=
  profile.intentWarrant h.right

def contestedDocumentedConceptProfile :
    ConceptAttributionProfile evidenceFormalContext :=
  { concept := documentedEvidenceConcept
    obj := EvidenceObject.recordA
    attr := EvidenceAttribute.contested
    mechanism := ISFTMechanism.M7
    objectInExtent := documentedEvidenceConcept_extent_contains_recordA
    attributeInIntent :=
      documentedEvidenceConcept.intent EvidenceAttribute.contested
    intentWarrant := fun h => h }

theorem contestedDocumentedConceptProfile_blocked :
    ConceptAttributionBlocked contestedDocumentedConceptProfile :=
  missing_intent_blocks_concept_attribution
    contestedDocumentedConceptProfile
    documentedEvidenceConcept_intent_not_contested

theorem contestedDocumentedConceptProfile_not_satisfied :
    Not (ConceptAttributionSatisfied contestedDocumentedConceptProfile) := by
  intro h
  exact documentedEvidenceConcept_intent_not_contested h.right

def documentedDocumentedConceptProfile :
    ConceptAttributionProfile evidenceFormalContext :=
  { concept := documentedEvidenceConcept
    obj := EvidenceObject.recordA
    attr := EvidenceAttribute.documented
    mechanism := ISFTMechanism.M7
    objectInExtent := documentedEvidenceConcept_extent_contains_recordA
    attributeInIntent :=
      documentedEvidenceConcept.intent EvidenceAttribute.documented
    intentWarrant := fun h => h }

theorem documentedDocumentedConceptProfile_satisfied :
    ConceptAttributionSatisfied documentedDocumentedConceptProfile :=
  And.intro rfl documentedEvidenceConcept_intent_has_documented

end Paralogic
