import Paralogic.FrameContext
import Paralogic.ManySortedCountermodels
import Paralogic.NontrivialFiniteModels

/-!
Non-preservation witnesses.

These results prevent a reward-hacking move: treating every typed carrier map
as if it preserved semantic content. Preservation requires explicit
homomorphism obligations.
-/

namespace Paralogic

def emptySemanticModel : SigmaModel :=
  UnitPredicateModel (fun _ => False)

def erasingSortMap : SortMap usesOnlySemanticModel emptySemanticModel where
  map := fun _ _ => Unit.unit

theorem erasingSortMap_source_has_UsesSem :
    UsesSem (M := usesOnlySemanticModel) Unit.unit Unit.unit :=
  usesOnlySemantic_has_UsesSem

theorem erasingSortMap_target_not_UsesSem :
    Not (UsesSem (M := emptySemanticModel) Unit.unit Unit.unit) := by
  intro h
  exact h

theorem erasingSortMap_not_ModelHom :
    Not (Exists (fun h : ModelHom usesOnlySemanticModel emptySemanticModel =>
      forall (s : SortTag) (x : usesOnlySemanticModel.Carrier s),
        h.map s x = erasingSortMap.map s x)) := by
  intro hex
  exact Exists.elim hex
    (fun h _ =>
      erasingSortMap_target_not_UsesSem
        (ModelHom_preserves_UsesSem h erasingSortMap_source_has_UsesSem))

def unitUsesTermArgs : Args Term [SortTag.institution, SortTag.symbolicOutput] :=
  Args.cons (Term.var (s := SortTag.institution) 0)
    (Args.cons (Term.var (s := SortTag.symbolicOutput) 0) Args.nil)

def usesAtomFormula : Formula :=
  Formula.atom PredicateSymbol.uses unitUsesTermArgs

def negUsesAtomFormula : Formula :=
  Formula.neg usesAtomFormula

def usesImpliesFalsityFormula : Formula :=
  Formula.impl usesAtomFormula Formula.falsity

def emptyToUsesModelHom : ModelHom emptySemanticModel usesOnlySemanticModel :=
  { map := fun _ _ => Unit.unit
    preservesFunction := by
      intro _ args
      rfl
    preservesPredicate := by
      intro _ _ h
      exact False.elim h }

def emptySemanticAssignment : Assignment emptySemanticModel :=
  fun _ _ => Unit.unit

theorem model_hom_not_preserve_negation_counterexample :
    And
      (SatisfiesFormula emptySemanticAssignment negUsesAtomFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment emptyToUsesModelHom emptySemanticAssignment)
        negUsesAtomFormula)) :=
  And.intro
    (by
      intro h
      exact h)
    (by
      intro hNeg
      exact hNeg True.intro)

theorem model_hom_not_preserve_implication_counterexample :
    And
      (SatisfiesFormula emptySemanticAssignment usesImpliesFalsityFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment emptyToUsesModelHom emptySemanticAssignment)
        usesImpliesFalsityFormula)) :=
  And.intro
    (by
      intro h
      exact h)
    (by
      intro hImp
      exact hImp True.intro)

def BoolTrueFunctionPredicateModel
    (truth : (p : PredicateSymbol) ->
      Args BoolCarrier ((predicateArity p).domain) -> Prop) :
    SigmaModel :=
  { Carrier := BoolCarrier
    interpFunction := fun _ _ => true
    interpPredicate := truth }

def boolUsesTrueArgsTruth :
    (p : PredicateSymbol) -> Args BoolCarrier ((predicateArity p).domain) ->
      Prop
  | PredicateSymbol.uses, Args.cons institution
      (Args.cons output Args.nil) =>
      And (institution = true) (output = true)
  | _, _ => False

def boolUsesTrueArgsModel : SigmaModel :=
  BoolTrueFunctionPredicateModel boolUsesTrueArgsTruth

def unitUsesOnlyModel : SigmaModel :=
  UnitPredicateModel (fun p => p = PredicateSymbol.uses)

def unitToBoolTrueHom : ModelHom unitUsesOnlyModel boolUsesTrueArgsModel :=
  { map := fun _ _ => true
    preservesFunction := by
      intro _ args
      rfl
    preservesPredicate := by
      intro predicate args h
      cases predicate <;> simp [unitUsesOnlyModel, UnitPredicateModel] at h
      cases args with
      | cons institution rest =>
          cases rest with
          | cons output rest =>
              cases rest
              exact And.intro rfl rfl }

def unitUsesOnlyAssignment : Assignment unitUsesOnlyModel :=
  fun _ _ => Unit.unit

def forallInstitutionUsesFormula : Formula :=
  Formula.forallVar SortTag.institution 0 usesAtomFormula

theorem model_hom_not_preserve_universal_counterexample :
    And
      (SatisfiesFormula unitUsesOnlyAssignment forallInstitutionUsesFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment unitToBoolTrueHom unitUsesOnlyAssignment)
        forallInstitutionUsesFormula)) :=
  And.intro
    (by
      intro value
      cases value
      exact rfl)
    (by
      intro hForall
      have hAtFalse := hForall false
      exact Bool.noConfusion hAtFalse.left)

def boolUsesTrueAssignment : Assignment boolUsesTrueArgsModel :=
  fun _ _ => true

theorem boolUsesTrueAssignment_satisfies_usesAtom :
    SatisfiesFormula boolUsesTrueAssignment usesAtomFormula := by
  exact And.intro rfl rfl

theorem boolUsesTrueAssignment_not_forallInstitutionUses :
    Not (SatisfiesFormula boolUsesTrueAssignment forallInstitutionUsesFormula) := by
  intro hForall
  have hAtFalse := hForall false
  exact Bool.noConfusion hAtFalse.left

def universal_intro_without_freshness_countermodel :
    SemanticCountermodel [usesAtomFormula] forallInstitutionUsesFormula :=
  { M := boolUsesTrueArgsModel
    rho := boolUsesTrueAssignment
    premisesTrue :=
      And.intro boolUsesTrueAssignment_satisfies_usesAtom True.intro
    conclusionFalse := boolUsesTrueAssignment_not_forallInstitutionUses }

theorem universal_intro_without_freshness_not_semantically_valid :
    Not (SemanticallyEntails [usesAtomFormula] forallInstitutionUsesFormula) := by
  intro hEntails
  exact universal_intro_without_freshness_countermodel.conclusionFalse
    (hEntails
      universal_intro_without_freshness_countermodel.M
      universal_intro_without_freshness_countermodel.rho
      universal_intro_without_freshness_countermodel.premisesTrue)

end Paralogic
