import Paralogic.ModelSemantics

/-!
Independent many-sorted countermodel families.

These witnesses live directly in the `SigmaModel` layer. They do not depend on
the old one-object `World` kernel.
-/

namespace Paralogic

def usesOnlySemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | _ => False

def usesOnlySemanticModel : SigmaModel :=
  UnitPredicateModel usesOnlySemanticTruth

theorem usesOnlySemantic_has_UsesSem :
    UsesSem (M := usesOnlySemanticModel) Unit.unit Unit.unit :=
  True.intro

theorem usesOnlySemantic_not_ISFSem :
    Not (ISFSem usesOnlySemanticModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h.claims

def claimsOnlySemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.claims => True
  | _ => False

def claimsOnlySemanticModel : SigmaModel :=
  UnitPredicateModel claimsOnlySemanticTruth

theorem claimsOnlySemantic_has_ClaimsSem :
    ClaimsSem (M := claimsOnlySemanticModel) Unit.unit Unit.unit Unit.unit :=
  True.intro

theorem claimsOnlySemantic_not_ISFSem :
    Not (ISFSem claimsOnlySemanticModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.uses

def supportOnlySemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.supportDegraded => True
  | _ => False

def supportOnlySemanticModel : SigmaModel :=
  UnitPredicateModel supportOnlySemanticTruth

theorem supportOnlySemantic_has_SupportDegradedSem :
    SupportDegradedSem (M := supportOnlySemanticModel) Unit.unit Unit.unit
      Unit.unit :=
  True.intro

theorem supportOnlySemantic_not_ISFSem :
    Not (ISFSem supportOnlySemanticModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.uses

def noTreatmentSemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | _ => False

def noTreatmentSemanticModel : SigmaModel :=
  UnitPredicateModel noTreatmentSemanticTruth

theorem noTreatmentSemantic_has_uses_claims_support :
    UsesSem (M := noTreatmentSemanticModel) Unit.unit Unit.unit ∧
    ClaimsSem (M := noTreatmentSemanticModel) Unit.unit Unit.unit Unit.unit ∧
    SupportDegradedSem (M := noTreatmentSemanticModel) Unit.unit Unit.unit
      Unit.unit :=
  And.intro True.intro (And.intro True.intro True.intro)

theorem noTreatmentSemantic_not_ISFSem :
    Not (ISFSem noTreatmentSemanticModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.treatsAsAdequate

def isfNotM8SemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def isfNotM8SemanticModel : SigmaModel :=
  UnitPredicateModel isfNotM8SemanticTruth

theorem isfNotM8Semantic_is_ISFSem :
    ISFSem isfNotM8SemanticModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  { uses := True.intro
    claims := True.intro
    supportDegraded := True.intro
    treatsAsAdequate := True.intro }

theorem isfNotM8Semantic_not_M8Sem :
    Not (M8Sem isfNotM8SemanticModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h.powerRelevant

def deltaOnlySemanticTruth : PredicateSymbol -> Prop
  | PredicateSymbol.contradictionPresent => True
  | _ => False

def deltaOnlySemanticModel : SigmaModel :=
  UnitPredicateModel deltaOnlySemanticTruth

theorem deltaOnlySemantic_not_ValidInsightSem :
    Not (ValidInsightSem deltaOnlySemanticModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

end Paralogic
