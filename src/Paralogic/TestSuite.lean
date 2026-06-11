import Paralogic.Theorems
import Paralogic.ProofTheory
import Paralogic.FrameContext
import Paralogic.NonPreservation
import Paralogic.ContextualObstruction
import Paralogic.DeltaDynamics
import Paralogic.MinimalRepair
import Paralogic.Argumentation
import Paralogic.NontrivialFiniteModels
import Paralogic.RoughEvidence
import Paralogic.RoughAdequacyBridge
import Paralogic.EvidenceGranularity
import Paralogic.EvaluatorCalibration
import Paralogic.EvaluatorArgumentation
import Paralogic.InstitutionFragment
import Paralogic.FormalConcept
import Paralogic.ConceptualEssentialization
import Paralogic.MechanismSynthesis
import Paralogic.EvidenceOverclaim
import Paralogic.MetricProxy
import Paralogic.FormalAccessSubstitution
import Paralogic.SymbolicSubstitution
import Paralogic.RepairFailure
import Paralogic.WarrantDischarge

/-!
Lean examples that serve as regression tests.

If any example fails, `lake build` fails.
-/

namespace Paralogic

example {w : World} (h : ISF w) : w.uses := ISF_to_Uses h
example {w : World} (h : ISF w) : w.claims := ISF_to_Claims h
example {w : World} (h : M8 w) : ISF w := M8_to_ISF h
example {w : World} (h : ValidInsight w) : w.evaluatorAccepts :=
  ValidInsight_to_EvaluatorAccepts h

example : usesOnlyWorld.uses ∧ ¬ ISF usesOnlyWorld :=
  ISF_does_not_follow_from_Uses

example : ISF isfNotM8World ∧ ¬ M8 isfNotM8World :=
  ISF_does_not_imply_M8

example : M8 m8NoBridgeWorld ∧ ¬ m8NoBridgeWorld.harm :=
  M8_does_not_imply_harm

example :
    ValidInsight validInsightNoBridgeWorld ∧
    ¬ validInsightNoBridgeWorld.empiricalTruth :=
  ValidInsight_does_not_imply_empiricalTruth

example :
    empiricalValidationNoLegitimacyWorld.empiricalValidation ∧
    ¬ empiricalValidationNoLegitimacyWorld.governanceLegitimacy :=
  EmpiricalValidation_does_not_imply_governanceLegitimacy

example (left right : Formula) :
    SemanticallyEntails [Formula.conj left right] left :=
  derives_conj_left_example_sound left right

example (left right : Formula) :
    SemanticallyEntails [Formula.impl left right, left] right :=
  derives_modus_ponens_example_sound left right

example (left right : Formula) :
    SemanticallyEntails [right] (Formula.impl left right) :=
  derives_implication_intro_example_sound left right

example (formula : Formula) :
    SemanticallyEntails [Formula.falsity] formula :=
  derives_falsity_elim_example_sound formula

example (left right conclusion : Formula) :
    SemanticallyEntails
      [Formula.disj left right,
        Formula.impl left conclusion,
        Formula.impl right conclusion]
      conclusion :=
  derives_disj_elim_example_sound left right conclusion

example (premises extra : List Formula) (conclusion : Formula)
    (h : Derives premises conclusion) :
    SemanticallyEntails (premises ++ extra) conclusion :=
  derives_append_monotone_right_sound (extra := extra) h

example (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [Formula.forallVar s idx body] body :=
  semantically_entails_forall_current s idx body

example (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [body] (Formula.existsVar s idx body) :=
  semantically_entails_exists_current s idx body

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  semantically_entails_forall_intro_of_stable
    (premises_stable_nil s idx)
    (semantically_entails_truth [])

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  semantically_entails_forall_intro_of_quantifier_free_fresh
    (by
      intro _ hMem
      cases hMem)
    (semantically_entails_truth [])

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  semantically_entails_forall_intro_of_fresh
    (by
      intro _ hMem
      cases hMem)
    (semantically_entails_truth [])

example (s : SortTag) (idx : Nat) (body : Formula) :
    Derives [Formula.forallVar s idx body] body :=
  derives_forall_current_example s idx body

example (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [Formula.forallVar s idx body] body :=
  derives_forall_current_example_sound s idx body

example (s : SortTag) (idx : Nat) (body : Formula) :
    Derives [body] (Formula.existsVar s idx body) :=
  derives_exists_current_example s idx body

example (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [body] (Formula.existsVar s idx body) :=
  derives_exists_current_example_sound s idx body

example (s : SortTag) (idx : Nat) :
    PremisesStableUnderUpdate s idx [] :=
  premises_stable_nil s idx

example (s : SortTag) (idx : Nat) :
    PremisesQuantifierFreeFreshForUpdate s idx [] := by
  intro _ hMem
  cases hMem

example (s : SortTag) (idx : Nat) :
    PremisesFreshForUpdate s idx [] := by
  intro _ hMem
  cases hMem

example (s : SortTag) (idx : Nat) :
    PremisesStableUnderUpdate s idx [] :=
  premises_stable_of_quantifier_free_fresh s idx []
    (by
      intro _ hMem
      cases hMem)

example (s : SortTag) (idx : Nat) :
    PremisesStableUnderUpdate s idx [] :=
  premises_stable_of_fresh s idx []
    (by
      intro _ hMem
      cases hMem)

example {M : SigmaModel} (rho : Assignment M)
    (s : SortTag) (idx : Nat) (value : M.Carrier s)
    (body : Formula) :
    Iff
      (SatisfiesFormula rho (Formula.forallVar s idx body))
      (SatisfiesFormula (updateAssignment rho s idx value)
        (Formula.forallVar s idx body)) :=
  satisfaction_stable_update_of_not_free rho s idx value
    (Formula.forallVar s idx body)
    (quantified_variable_not_free_forall s idx body)

example {M : SigmaModel} (rho sigma : Assignment M) :
    AssignmentsAgreeOnFormula rho sigma Formula.truth :=
  closed_formula_assignments_agree rho sigma Formula.truth
    (by
      intro _ _ hFree
      cases hFree)

example {M : SigmaModel} (rho sigma : Assignment M) :
    Iff (SatisfiesFormula rho Formula.truth)
      (SatisfiesFormula sigma Formula.truth) :=
  closed_formula_satisfaction_invariant rho sigma Formula.truth
    (by
      intro _ _ hFree
      cases hFree)

example (s : SortTag) (idx : Nat) :
    FormulaClosed (Formula.forallVar s idx Formula.truth) := by
  intro target targetIdx hFree
  by_cases hBinder : And (s = target) (idx = targetIdx)
  · simp [FormulaHasFreeVar, hBinder] at hFree
  · simp [FormulaHasFreeVar, hBinder] at hFree

example {M : SigmaModel} (rho sigma : Assignment M)
    (s : SortTag) (idx : Nat) :
    Iff (SatisfiesFormula rho (Formula.forallVar s idx Formula.truth))
      (SatisfiesFormula sigma (Formula.forallVar s idx Formula.truth)) :=
  closed_formula_satisfaction_invariant rho sigma
    (Formula.forallVar s idx Formula.truth)
    (by
      intro target targetIdx hFree
      by_cases hBinder : And (s = target) (idx = targetIdx)
      · simp [FormulaHasFreeVar, hBinder] at hFree
      · simp [FormulaHasFreeVar, hBinder] at hFree)

example :
    PremisesClosed [] :=
  premises_closed_nil

example :
    PremisesClosed [Formula.truth] :=
  premises_closed_cons
    (by
      intro _ _ hFree
      cases hFree)
    premises_closed_nil

example {M : SigmaModel} (rho sigma : Assignment M) :
    Iff (SatisfiesAll rho [Formula.truth])
      (SatisfiesAll sigma [Formula.truth]) :=
  closed_premises_satisfaction_invariant rho sigma [Formula.truth]
    (premises_closed_cons
      (by
        intro _ _ hFree
        cases hFree)
      premises_closed_nil)

example (s : SortTag) (idx : Nat) :
    Derives [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_truth_example s idx

example (s : SortTag) (idx : Nat) :
    Derives [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_intro_of_quantifier_free_fresh
    (by
      intro _ hMem
      cases hMem)
    Derives.truth

example (s : SortTag) (idx : Nat) :
    Derives [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_intro_of_fresh
    (by
      intro _ hMem
      cases hMem)
    Derives.truth

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_truth_example_sound s idx

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_intro_of_quantifier_free_fresh_sound
    (by
      intro _ hMem
      cases hMem)
    Derives.truth

example (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  derives_forall_intro_of_fresh_sound
    (by
      intro _ hMem
      cases hMem)
    Derives.truth

example (left right : Bool) :
    HasGlobalExtension (boolPairFamily left right) :=
  boolPairFamily_has_global_extension left right

example {M N P Q : SigmaModel}
    (h : ModelHom P Q) (g : ModelHom N P) (f : ModelHom M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeModelHom h (composeModelHom g f)).map s x =
      (composeModelHom (composeModelHom h g) f).map s x :=
  composeModelHom_assoc_map h g f s x

example {M N : SigmaModel} (h : ModelHom M N) (rho : Assignment M)
    (formula : Formula)
    (hPositive : PositiveQuantifierFreeFormula formula)
    (hs : SatisfiesFormula rho formula) :
    SatisfiesFormula (ModelHom.mapAssignment h rho) formula :=
  ModelHom_preserves_positive_quantifier_free_satisfaction h rho formula
    hPositive hs

example (M : SigmaModel) :
    ModelIso M M :=
  identityModelIso M

example {M N P : SigmaModel}
    (second : ModelIso N P) (first : ModelIso M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeModelIso second first).forward.map s x =
      second.forward.map s (first.forward.map s x) :=
  composeModelIso_forward_map second first s x

example {M N : SigmaModel}
    (iso : ModelIso M N)
    (predicate : PredicateSymbol)
    (args : Args M.Carrier ((predicateArity predicate).domain))
    (hTarget :
      N.interpPredicate predicate
        (Args.map (fun {s} x => iso.forward.map s x) args)) :
    M.interpPredicate predicate args :=
  ModelIso_reflectsPredicate iso predicate args hTarget

example {M N : SigmaModel} (iso : ModelIso M N) (rho : Assignment M)
    (formula : Formula)
    (hPositive : PositiveQuantifierFreeFormula formula) :
    Iff (SatisfiesFormula rho formula)
      (SatisfiesFormula (ModelHom.mapAssignment iso.forward rho) formula) :=
  ModelIso_positive_quantifier_free_satisfaction_iff iso rho formula
    hPositive

example {M N : SigmaModel} (iso : ModelIso M N) (rho : Assignment M)
    (formula : Formula) :
    Iff (SatisfiesFormula rho formula)
      (SatisfiesFormula (ModelHom.mapAssignment iso.forward rho) formula) :=
  ModelIso_full_formula_satisfaction_iff iso rho formula

example {M N : SigmaModel} (iso : ModelIso M N) (rho : Assignment M)
    (s : SortTag) (idx : Nat) (value : N.Carrier s) :
    updateAssignment (ModelHom.mapAssignment iso.forward rho) s idx value =
      ModelHom.mapAssignment iso.forward
        (updateAssignment rho s idx (iso.backward.map s value)) :=
  ModelIso_forward_updateAssignment iso rho s idx value

example (M : SigmaModel) (formula : Formula) :
    (identityFormulaTranslation M).translateFormula formula = formula :=
  identityFormulaTranslation_apply M formula

example {M N P : SigmaModel}
    (second : FormulaTranslation N P)
    (first : FormulaTranslation M N)
    (formula : Formula) :
    (composeFormulaTranslation second first).translateFormula formula =
      second.translateFormula (first.translateFormula formula) :=
  composeFormulaTranslation_apply second first formula

example {M N : SigmaModel}
    (translation : FormulaTranslation M N)
    (rho : Assignment M)
    (premises : List Formula)
    (hAll : SatisfiesAll rho premises) :
    SatisfiesAll (translation.translateAssignment rho)
      (translation.translatePremises premises) :=
  FormulaTranslation_preserves_satisfies_all translation rho premises hAll

example {M N : SigmaModel}
    (translation : FormulaTranslation M N)
    (premises : List Formula)
    (conclusion : Formula)
    (hEntails : SemanticallyEntails premises conclusion)
    (rho : Assignment M)
    (hAll : SatisfiesAll rho premises) :
    And
      (SatisfiesAll (translation.translateAssignment rho)
        (translation.translatePremises premises))
      (SatisfiesFormula (translation.translateAssignment rho)
        (translation.translateFormula conclusion)) :=
  FormulaTranslation_transports_semantic_entailment_instance
    translation hEntails rho hAll

example :
    And
      (SatisfiesFormula emptySemanticAssignment negUsesAtomFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment emptyToUsesModelHom emptySemanticAssignment)
        negUsesAtomFormula)) :=
  model_hom_not_preserve_negation_counterexample

example :
    And
      (SatisfiesFormula emptySemanticAssignment usesImpliesFalsityFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment emptyToUsesModelHom emptySemanticAssignment)
        usesImpliesFalsityFormula)) :=
  model_hom_not_preserve_implication_counterexample

example :
    And
      (SatisfiesFormula unitUsesOnlyAssignment forallInstitutionUsesFormula)
      (Not (SatisfiesFormula
        (ModelHom.mapAssignment unitToBoolTrueHom unitUsesOnlyAssignment)
        forallInstitutionUsesFormula)) :=
  model_hom_not_preserve_universal_counterexample

example :
    SatisfiesFormula boolUsesTrueAssignment usesAtomFormula :=
  boolUsesTrueAssignment_satisfies_usesAtom

example :
    Not (SatisfiesFormula boolUsesTrueAssignment forallInstitutionUsesFormula) :=
  boolUsesTrueAssignment_not_forallInstitutionUses

example :
    SemanticCountermodel [usesAtomFormula] forallInstitutionUsesFormula :=
  universal_intro_without_freshness_countermodel

example :
    Not (SemanticallyEntails [usesAtomFormula] forallInstitutionUsesFormula) :=
  universal_intro_without_freshness_not_semantically_valid

example :
    mechanismLens ISFTMechanism.M2 = MechanismLens.metricProxy :=
  M2_lens_is_metric_proxy

example :
    mechanismFailureAxis ISFTMechanism.M10 =
      CandidateFailureAxis.contextFrameDrift :=
  rfl

example :
    CandidateMechanismDefinitionSatisfied
      (unitCandidateDefinition ISFTMechanism.M1) :=
  unit_candidate_definition_satisfied ISFTMechanism.M1

example :
    ISFTMechanismProfileSatisfied
      (unitCandidateDefinition ISFTMechanism.M12).toMechanismProfile :=
  unit_candidate_profile_satisfied ISFTMechanism.M12

example :
    Not
      ((unitCandidateDefinition ISFTMechanism.M8).maturity =
        MechanismSemanticMaturity.sourceBacked) :=
  candidate_synthesized_not_source_backed
    (unitCandidateDefinition ISFTMechanism.M8)
    rfl

example :
    allISFTMechanisms.length = 12 :=
  allISFTMechanisms_length

example (mechanism : ISFTMechanism) :
    mechanism ∈ allISFTMechanisms :=
  allISFTMechanisms_covers mechanism

example (mechanism : ISFTMechanism) :
    CandidateMechanismMappingCertified mechanism :=
  unit_candidate_mapping_certified mechanism

example (mechanism : ISFTMechanism) :
    CandidateMechanismSurfaceCertified mechanism :=
  unit_candidate_surface_certified mechanism

example :
    CandidateMechanismCoverageComplete :=
  candidate_mechanism_coverage_complete

example (mechanism : ISFTMechanism) :
    Not
      ((unitCandidateDefinition mechanism).maturity =
        MechanismSemanticMaturity.empiricallyValidated) :=
  all_candidate_mechanisms_not_empirically_validated mechanism

example :
    EvidenceOverclaimProfileSatisfied evidenceOverclaimOnlyProfile :=
  evidenceOverclaimOnlyProfile_satisfied

example :
    SupportDegradedSem (M := evidenceOverclaimOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  evidenceOverclaimOnly_supportDegraded

example :
    ISFSem evidenceOverclaimOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  evidenceOverclaimOnly_to_ISFSem

example :
    ISFTMechanismProfileSatisfied
      evidenceOverclaimOnlyProfile.toMechanismProfile :=
  evidenceOverclaimOnly_mechanism_profile_satisfied

example :
    (evidenceOverclaimOnlyProfile.toMechanismProfile).mechanism =
      ISFTMechanism.M1 :=
  EvidenceOverclaimProfile_mechanism_label evidenceOverclaimOnlyProfile

example :
    EvidenceOverclaimProfileBlocked evidenceOverclaimNoScopeProfile :=
  evidenceOverclaimNoScopeProfile_blocked

example :
    EvidenceOverclaimProfileBlocked evidenceOverclaimIrrelevantProfile :=
  evidenceOverclaimIrrelevantProfile_blocked

example :
    EvidenceOverclaimProfileBlocked evidenceOverclaimSufficientProfile :=
  evidenceOverclaimSufficientProfile_blocked

example :
    EvidenceOverclaimProfileBlocked evidenceOverclaimMatchedScopeProfile :=
  evidenceOverclaimMatchedScopeProfile_blocked

example :
    EvidenceOverclaimProfileBlocked
      evidenceOverclaimBoundedUncertaintyProfile :=
  evidenceOverclaimBoundedUncertaintyProfile_blocked

example :
    EvidenceOverclaimProfileBlocked evidenceOverclaimImmaterialProfile :=
  evidenceOverclaimImmaterialProfile_blocked

example :
    EvidenceOverclaimProfileBlocked
      evidenceOverclaimBoundaryPresentProfile :=
  evidenceOverclaimBoundaryPresentProfile_blocked

example :
    FormalAccessProfileSatisfied formalAccessOnlyProfile :=
  formalAccessOnlyProfile_satisfied

example :
    SupportDegradedSem (M := formalAccessOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  formalAccessOnly_supportDegraded

example :
    ISFSem formalAccessOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  formalAccessOnly_to_ISFSem

example :
    ISFTMechanismProfileSatisfied
      formalAccessOnlyProfile.toMechanismProfile :=
  formalAccessOnly_mechanism_profile_satisfied

example :
    (formalAccessOnlyProfile.toMechanismProfile).mechanism =
      ISFTMechanism.M3 :=
  FormalAccessProfile_mechanism_label formalAccessOnlyProfile

example :
    FormalAccessProfileBlocked formalAccessNoDeclarationProfile :=
  formalAccessNoDeclarationProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessSubstantivePresentProfile :=
  formalAccessSubstantivePresentProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessNotSubstitutedProfile :=
  formalAccessNotSubstitutedProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessUsableProfile :=
  formalAccessUsableProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessComprehensibleProfile :=
  formalAccessComprehensibleProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessRemedyPresentProfile :=
  formalAccessRemedyPresentProfile_blocked

example :
    FormalAccessProfileBlocked formalAccessBoundaryPresentProfile :=
  formalAccessBoundaryPresentProfile_blocked

example :
    SymbolicSubstitutionProfileSatisfied
      symbolicSubstitutionOnlyProfile :=
  symbolicSubstitutionOnlyProfile_satisfied

example :
    SupportDegradedSem (M := symbolicSubstitutionOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  symbolicSubstitutionOnly_supportDegraded

example :
    ISFSem symbolicSubstitutionOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  symbolicSubstitutionOnly_to_ISFSem

example :
    ISFTMechanismProfileSatisfied
      symbolicSubstitutionOnlyProfile.toMechanismProfile :=
  symbolicSubstitutionOnly_mechanism_profile_satisfied

example :
    (symbolicSubstitutionOnlyProfile.toMechanismProfile).mechanism =
      ISFTMechanism.M4 :=
  SymbolicSubstitutionProfile_mechanism_label
    symbolicSubstitutionOnlyProfile

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionNoSymbolProfile :=
  symbolicSubstitutionNoSymbolProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionNotSubstantiveProfile :=
  symbolicSubstitutionNotSubstantiveProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionMatchedProfile :=
  symbolicSubstitutionMatchedProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionMaterialPresentProfile :=
  symbolicSubstitutionMaterialPresentProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionImmaterialUptakeProfile :=
  symbolicSubstitutionImmaterialUptakeProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionCorrectionPresentProfile :=
  symbolicSubstitutionCorrectionPresentProfile_blocked

example :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionBoundaryPresentProfile :=
  symbolicSubstitutionBoundaryPresentProfile_blocked

example :
    RepairFailureProfileSatisfied repairFailureOnlyProfile :=
  repairFailureOnlyProfile_satisfied

example :
    SupportDegradedSem (M := repairFailureOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  repairFailureOnly_supportDegraded

example :
    ISFSem repairFailureOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  repairFailureOnly_to_ISFSem

example :
    ISFTMechanismProfileSatisfied
      repairFailureOnlyProfile.toMechanismProfile :=
  repairFailureOnly_mechanism_profile_satisfied

example :
    (repairFailureOnlyProfile.toMechanismProfile).mechanism =
      ISFTMechanism.M5 :=
  RepairFailureProfile_mechanism_label repairFailureOnlyProfile

example :
    RepairFailureProfileBlocked repairFailureNoNeedProfile :=
  repairFailureNoNeedProfile_blocked

example :
    RepairFailureProfileBlocked repairFailureNoResponsibilityProfile :=
  repairFailureNoResponsibilityProfile_blocked

example :
    RepairFailureProfileBlocked repairFailurePlanPresentProfile :=
  repairFailurePlanPresentProfile_blocked

example :
    RepairFailureProfileBlocked repairFailureActionSuccessfulProfile :=
  repairFailureActionSuccessfulProfile_blocked

example :
    RepairFailureProfileBlocked repairFailureVerifiedProfile :=
  repairFailureVerifiedProfile_blocked

example :
    RepairFailureProfileBlocked repairFailureNoRecurrenceProfile :=
  repairFailureNoRecurrenceProfile_blocked

example :
    RepairFailureProfileBlocked repairFailureNoClosureClaimProfile :=
  repairFailureNoClosureClaimProfile_blocked

example :
    MetricProxyProfileSatisfied metricProxyOnlyProfile :=
  metricProxyOnlyProfile_satisfied

example :
    SupportDegradedSem (M := metricProxyOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  metricProxyOnly_supportDegraded

example :
    ISFSem metricProxyOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  metricProxyOnly_to_ISFSem

example :
    ISFTMechanismProfileSatisfied
      metricProxyOnlyProfile.toMechanismProfile :=
  metricProxyOnly_mechanism_profile_satisfied

example :
    (metricProxyOnlyProfile.toMechanismProfile).mechanism =
      ISFTMechanism.M2 :=
  MetricProxyProfile_mechanism_label metricProxyOnlyProfile

example :
    MetricProxyProfileBlocked metricProxyNoTargetProfile :=
  metricProxyNoTargetProfile_blocked

example :
    MetricProxyProfileBlocked metricProxyUnusedProfile :=
  metricProxyUnusedProfile_blocked

example :
    MetricProxyProfileBlocked metricProxyNoPressureProfile :=
  metricProxyNoPressureProfile_blocked

example :
    MetricProxyProfileBlocked metricProxyAlignedProfile :=
  metricProxyAlignedProfile_blocked

example :
    MetricProxyProfileBlocked metricProxyImmaterialProfile :=
  metricProxyImmaterialProfile_blocked

example :
    MetricProxyProfileBlocked metricProxyGuardedProfile :=
  metricProxyGuardedProfile_blocked

example :
    MetricProxyProfileBlocked metricProxySeparatedProfile :=
  metricProxySeparatedProfile_blocked

example :
    warrantResolutionStatus WarrantObligation.adequacy =
      WarrantResolutionStatus.countermodelGuarded :=
  rfl

example :
    warrantResolutionStatusWithOperationalAdequacy WarrantObligation.adequacy =
      WarrantResolutionStatus.operationallyDischarged :=
  adequacy_is_operationally_discharged_in_scoped_model

example :
    warrantResolutionStatusWithOperationalAdequacyAndEvaluator
      WarrantObligation.evaluatorDecisionAccepts =
        WarrantResolutionStatus.operationallyDischarged :=
  rfl

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.contradictionPresent =
        WarrantResolutionStatus.operationallyDischarged :=
  contradiction_is_operationally_discharged_in_scoped_model

example :
    ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.contestedClaim :=
  operational_contradiction_active_contested_present

example :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.resolvedClaim) :=
  operational_contradiction_resolved_not_present

example :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.inactiveFrame
      OperationalContradictionToken.activeContext
      OperationalContradictionToken.contestedClaim) :=
  operational_contradiction_inactive_frame_not_present

example :
    Not (ContradictionPresentSem (M := operationalContradictionModel)
      OperationalContradictionToken.activeFrame
      OperationalContradictionToken.inactiveContext
      OperationalContradictionToken.contestedClaim) :=
  operational_contradiction_inactive_context_not_present

example :
    ContradictionProfileSatisfied operationalContradictionProfile :=
  operationalContradictionProfile_satisfied

example :
    ContradictionPresentSem (M := operationalContradictionModel)
      operationalContradictionProfile.frame
      operationalContradictionProfile.context
      operationalContradictionProfile.claim :=
  operationalContradictionProfile_to_present

example :
    operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons OperationalAdequacyToken.supported
        (Args.cons OperationalAdequacyToken.inScope
          (Args.cons OperationalAdequacyToken.matched Args.nil))) :=
  operational_adequacy_supported_in_scope_matched

example :
    Not (operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons OperationalAdequacyToken.unsupported
        (Args.cons OperationalAdequacyToken.inScope
          (Args.cons OperationalAdequacyToken.matched Args.nil)))) :=
  operational_adequacy_unsupported_not_adequate

example :
    AdequacyProfileSatisfied operationalAdequacyProfile :=
  operationalAdequacyProfile_satisfied

example :
    operationalAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons operationalAdequacyProfile.evidence
        (Args.cons operationalAdequacyProfile.context
          (Args.cons operationalAdequacyProfile.claim Args.nil))) :=
  operationalAdequacyProfile_to_adequate

example :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      OperationalEvaluatorToken.approvedEvaluator
      OperationalEvaluatorToken.approvedCandidate :=
  operational_evaluator_high_pair_accepts

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.evaluatorCriteriaAccepts =
        WarrantResolutionStatus.operationallyDischarged :=
  evaluator_criteria_is_operationally_discharged_in_scoped_model

example :
    EvaluatorCriteriaSatisfied operationalEvaluatorCriteria :=
  operationalEvaluatorCriteria_satisfied

example :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      operationalEvaluatorCriteria.evaluator
      operationalEvaluatorCriteria.candidate :=
  operationalEvaluatorCriteria_accepts

example :
    Not (EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      OperationalEvaluatorToken.approvedEvaluator
      OperationalEvaluatorToken.rejectedCandidate) :=
  operational_evaluator_rejected_candidate_not_accepted

example :
    EvaluatorDecisionSatisfied operationalHighScoreDecision :=
  operationalHighScoreDecision_satisfied

example :
    EvaluatorAcceptsSem (M := operationalEvaluatorModel)
      operationalHighScoreDecision.evaluator
      operationalHighScoreDecision.candidate :=
  operationalHighScoreDecision_accepts

example :
    Not (scoreDecision ScoreLevel.low = EvaluationValue.accepts) :=
  low_score_still_not_accepting_decision

example :
    PowerRelevantSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.affectedGroup :=
  operational_power_relevant

example :
    Not (PowerRelevantSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.unaffectedGroup) :=
  operational_power_unaffected_group_not_relevant

example :
    PowerValidityDependenceSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.materialPowerCondition :=
  operational_power_validity_dependence

example :
    Not (PowerValidityDependenceSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.immaterialPowerCondition) :=
  operational_power_immaterial_condition_not_dependence

example :
    PowerOmittedSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.contestedOutput
      OperationalPowerToken.materialPowerCondition :=
  operational_power_omitted

example :
    Not (PowerOmittedSem (M := operationalPowerModel)
      OperationalPowerToken.reviewInstitution
      OperationalPowerToken.ordinaryOutput
      OperationalPowerToken.materialPowerCondition) :=
  operational_power_ordinary_output_not_omitted

example :
    PowerConditionProfileSatisfied operationalPowerConditionProfile :=
  operationalPowerConditionProfile_satisfied

example :
    PowerRelevantSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.group :=
  operationalPowerConditionProfile_to_powerRelevant

example :
    PowerValidityDependenceSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.output
      operationalPowerConditionProfile.condition :=
  operationalPowerConditionProfile_to_powerValidityDependence

example :
    PowerOmittedSem (M := operationalPowerModel)
      operationalPowerConditionProfile.institution
      operationalPowerConditionProfile.output
      operationalPowerConditionProfile.condition :=
  operationalPowerConditionProfile_to_powerOmitted

example :
    warrantResolutionStatusWithOperationalCore WarrantObligation.powerRelevant =
      WarrantResolutionStatus.operationallyDischarged :=
  power_relevant_is_operationally_discharged_in_scoped_model

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.powerValidityDependence =
      WarrantResolutionStatus.operationallyDischarged :=
  power_validity_dependence_is_operationally_discharged_in_scoped_model

example :
    warrantResolutionStatusWithOperationalCore WarrantObligation.powerOmitted =
      WarrantResolutionStatus.operationallyDischarged :=
  power_omitted_is_operationally_discharged_in_scoped_model

example :
    SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.suppressedClaim :=
  operational_suppression_support_degraded

example :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.unsupportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.suppressedClaim) :=
  operational_suppression_unsupported_not_degraded

example :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.mismatchedContext
      OperationalSuppressionToken.suppressedClaim) :=
  operational_suppression_mismatched_context_not_degraded

example :
    Not (SupportDegradedSem (M := operationalSuppressionModel)
      OperationalSuppressionToken.supportedEvidence
      OperationalSuppressionToken.matchedContext
      OperationalSuppressionToken.ordinaryClaim) :=
  operational_suppression_ordinary_claim_not_degraded

example :
    SuppressionProfileSatisfied operationalSuppressionProfile :=
  operationalSuppressionProfile_satisfied

example :
    SupportDegradedSem (M := operationalSuppressionModel)
      operationalSuppressionProfile.evidence
      operationalSuppressionProfile.context
      operationalSuppressionProfile.claim :=
  operationalSuppressionProfile_to_supportDegraded

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.suppressionSupportDegraded =
      WarrantResolutionStatus.operationallyDischarged :=
  suppression_support_degraded_is_operationally_discharged_in_scoped_model

example :
    RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.affectedGroup :=
  operational_repair_obligation

example :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.ordinaryBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.affectedGroup) :=
  operational_repair_ordinary_bridge_not_obligation

example :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.otherInstitution
      OperationalRepairToken.affectedGroup) :=
  operational_repair_other_institution_not_obligation

example :
    Not (RepairObligationBridgeSem (M := operationalRepairModel)
      OperationalRepairToken.repairNeedBridge
      OperationalRepairToken.responsibleInstitution
      OperationalRepairToken.otherGroup) :=
  operational_repair_other_group_not_obligation

example :
    RepairDiagnosisSatisfied operationalRepairDiagnosis :=
  operationalRepairDiagnosis_satisfied

example :
    RepairObligationBridgeSem (M := operationalRepairModel)
      operationalRepairDiagnosis.bridge
      operationalRepairDiagnosis.institution
      operationalRepairDiagnosis.group :=
  operationalRepairDiagnosis_to_repairObligation

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.repairObligation =
      WarrantResolutionStatus.operationallyDischarged :=
  repair_obligation_is_operationally_discharged_in_scoped_model

example :
    FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.validatedObject
      OperationalEmpiricalToken.targetClaim :=
  operational_empirical_full_validation

example :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.nominalObject
      OperationalEmpiricalToken.targetClaim) :=
  operational_empirical_nominal_not_full

example :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.unvalidatedObject
      OperationalEmpiricalToken.targetClaim) :=
  operational_empirical_unvalidated_not_full

example :
    Not (FullEmpiricalValidationSem operationalEmpiricalModel
      OperationalEmpiricalToken.validatedObject
      OperationalEmpiricalToken.otherClaim) :=
  operational_empirical_other_claim_not_full

example :
    EmpiricalProtocolApplies operationalEmpiricalProtocol :=
  operationalEmpiricalProtocol_applies

example :
    FullEmpiricalValidationSem operationalEmpiricalModel
      operationalEmpiricalProtocol.validationObject
      operationalEmpiricalProtocol.targetClaim :=
  operationalEmpiricalProtocol_to_full_validation

example :
    warrantResolutionStatusWithOperationalCore
      WarrantObligation.empiricalFullValidation =
      WarrantResolutionStatus.operationallyDischarged :=
  empirical_full_validation_is_operationally_discharged_in_scoped_model

example (conclusion : NormativeConclusion) :
    NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeBridgeToken conclusion)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.affectedGroup :=
  operational_normative_conclusion conclusion

example (conclusion : NormativeConclusion) :
    BridgeApplies (operationalNormativeSchema conclusion) :=
  operationalNormativeSchema_applies conclusion

example (conclusion : NormativeConclusion) :
    NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeSchema conclusion).bridge
      (operationalNormativeSchema conclusion).institution
      (operationalNormativeSchema conclusion).group :=
  operationalNormativeSchema_to_conclusion conclusion

example (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      OperationalNormativeToken.ordinaryBridge
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.affectedGroup) :=
  operational_normative_ordinary_bridge_not_conclusion conclusion

example (conclusion : NormativeConclusion) :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      conclusion
      (operationalNormativeBridgeToken conclusion)
      OperationalNormativeToken.otherInstitution
      OperationalNormativeToken.affectedGroup) :=
  operational_normative_other_institution_not_conclusion conclusion

example :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      NormativeConclusion.harm
      (operationalNormativeBridgeToken NormativeConclusion.harm)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.otherGroup) :=
  operational_normative_harm_other_group_not_conclusion

example :
    Not (NormativeConclusionSem (M := operationalNormativeModel)
      NormativeConclusion.repairObligation
      (operationalNormativeBridgeToken NormativeConclusion.repairObligation)
      OperationalNormativeToken.responsibleInstitution
      OperationalNormativeToken.otherGroup) :=
  operational_normative_repair_other_group_not_conclusion

example :
    warrantResolutionStatusWithOperationalCore WarrantObligation.normativeBridge =
      WarrantResolutionStatus.operationallyDischarged :=
  normative_bridge_is_operationally_discharged_in_scoped_model

example :
    OperationalWarrantCoverageComplete :=
  operational_warrant_coverage_complete

example (obligation : WarrantObligation) :
    warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.operationallyDischarged :=
  all_warrant_obligations_operationally_discharged obligation

example (obligation : WarrantObligation) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.sourceBacked) :=
  operational_core_ne_source_backed obligation

example (obligation : WarrantObligation) :
    Not (warrantResolutionStatusWithOperationalCore obligation =
      WarrantResolutionStatus.empiricallyValidated) :=
  operational_core_ne_empirically_validated obligation

example :
    adequacy_warrant_countermodel.warrantedConclusionFails :=
  adequacy_warrant_countermodel_blocks_raw_shortcut

example :
    contradiction_warrant_countermodel.warrantedConclusionFails :=
  contradiction_warrant_countermodel_blocks_raw_shortcut

example :
    evaluator_criteria_warrant_countermodel.warrantedConclusionFails :=
  evaluator_warrant_countermodel_blocks_raw_shortcut

example :
    empirical_validation_warrant_countermodel.warrantedConclusionFails :=
  empirical_warrant_countermodel_blocks_raw_shortcut

example (conclusion : NormativeConclusion) :
    (normative_bridge_warrant_countermodel conclusion).warrantedConclusionFails :=
  normative_warrant_countermodel_blocks_raw_shortcut conclusion

example :
    repair_obligation_warrant_countermodel.warrantedConclusionFails :=
  repair_warrant_countermodel_blocks_raw_shortcut

example (obligation : WarrantObligation) :
    Not (warrantResolutionStatus obligation =
      WarrantResolutionStatus.sourceBacked) :=
  no_warrant_obligation_is_source_backed_yet obligation

example : ContextualObstruction noGlobalFamily :=
  noGlobalFamily_obstructed

example (system : DeltaTransitionSystem) :
    DeltaClosed system (DeltaReachable system) :=
  delta_reachable_closed system

example : EventuallyResolution twoDeltaSystem :=
  twoDelta_eventually_resolution

example :
    DeltaClosed twoDeltaSystem twoDeltaAllStates :=
  twoDelta_all_states_closed

example :
    Not (DeltaClosed twoDeltaSystem twoDeltaStartOnly) :=
  twoDelta_start_only_not_closed

example (candidate : TwoDeltaState -> Prop)
    (hClosed : DeltaClosed twoDeltaSystem candidate) :
    candidate TwoDeltaState.repaired :=
  twoDelta_repaired_in_every_closed candidate hClosed

example :
    And (EventuallyResolution twoDeltaSystem)
      (Not (DeltaGlobalFinality twoDeltaSystem)) :=
  eventual_resolution_not_global_finality

example :
    And
      (DeltaEventually twoDeltaSystem (IsResolutionState twoDeltaSystem))
      (Not (DeltaAlways twoDeltaSystem
        (IsResolutionState twoDeltaSystem))) :=
  eventual_not_always_resolution_modal

example :
    EventuallyStableResolution twoDeltaSystem :=
  twoDelta_eventually_stable_resolution

example :
    And (EventuallyStableResolution twoDeltaSystem)
      (Not (DeltaGlobalFinality twoDeltaSystem)) :=
  stable_resolution_not_global_finality

example : Not (EventuallyResolution loopDeltaSystem) :=
  loopDelta_not_eventually_resolution

example :
    And (EventuallyStable loopDeltaSystem)
      (Not (EventuallyResolution loopDeltaSystem)) :=
  eventual_stability_not_eventual_resolution

example :
    And
      (DeltaEventually loopDeltaSystem (IsStableState loopDeltaSystem))
      (Not (DeltaEventually loopDeltaSystem
        (IsResolutionState loopDeltaSystem))) :=
  eventual_stability_not_eventual_resolution_modal

example : HasMinimalRepair twoRepairFrame :=
  twoRepair_has_minimal

example : Not (HasUniqueMinimalRepair twoRepairFrame) :=
  twoRepair_not_unique_minimal

example : HasMinimalRepair rankedRepairFrame :=
  rankedRepair_has_minimal

example : HasUniqueMinimalRepair rankedRepairFrame :=
  rankedRepair_has_unique_minimal

example : HasUniqueMinimalRepair rankedRepairFrame :=
  rankedRepair_unique_minimal_from_best

example :
    RepairRevisionPostulates RepairRevisionAction.targetedAction :=
  targetedRepair_satisfies_revision_postulates

example :
    Not (RepairActionSuccessful RepairRevisionAction.partialAction) :=
  partialRepair_not_successful

example :
    And (RepairActionSuccessful RepairRevisionAction.excessiveAction)
      (Not (RepairActionMinimal RepairRevisionAction.excessiveAction)) :=
  excessiveRepair_successful_not_minimal

example :
    Not (RepairRevisionPostulates RepairRevisionAction.excessiveAction) :=
  excessiveRepair_not_revision_postulates

example :
    RepairObligationBridgeSem (M := repairBridgeOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  repairBridgeOnlyTargetedRevision_warrants_obligation

example :
    RepairPostulateIndependencePackage
      RepairPostulateAction.adequateAction :=
  adequateAction_satisfies_independence_package

example :
    And (RepairPostulateActionSuccessful
        RepairPostulateAction.redundantAction)
      (And (RepairPostulateActionConservative
          RepairPostulateAction.redundantAction)
        (Not (RepairPostulateActionMinimal
          RepairPostulateAction.redundantAction))) :=
  redundantAction_success_conservative_not_minimal

example :
    And (RepairPostulateActionSuccessful
        RepairPostulateAction.overreachAction)
      (And (RepairPostulateActionMinimal
          RepairPostulateAction.overreachAction)
        (Not (RepairPostulateActionConservative
          RepairPostulateAction.overreachAction))) :=
  overreachAction_success_minimal_not_conservative

example :
    And (RepairPostulateActionConservative
        RepairPostulateAction.failedAction)
      (Not (RepairPostulateActionSuccessful
        RepairPostulateAction.failedAction)) :=
  failedAction_conservative_not_successful

example : ConflictFree twoArgumentFramework targetOnlySelection :=
  targetOnly_conflict_free

example : Not (Admissible twoArgumentFramework targetOnlySelection) :=
  targetOnly_not_admissible

example : UsesSem (M := twoUsesOnlyModel) true false :=
  twoUsesOnly_has_UsesSem

example : Not (ISFSem twoUsesOnlyModel true false true false true) :=
  twoUsesOnly_not_ISFSem

example : ISFSem twoISFNotM8Model true false true false true :=
  twoISFNotM8_is_ISFSem

example : Not (M8Sem twoISFNotM8Model true false true false true false true) :=
  twoISFNotM8_not_M8Sem

example : BoundaryRegion twoEvidenceSpace TwoEvidence.favorable :=
  twoEvidence_favorable_boundary

example : BoundaryRegion twoEvidenceSpace TwoEvidence.unfavorable :=
  twoEvidence_unfavorable_boundary

example :
    Not (RoughAdequacyEligible twoEvidenceSpace TwoEvidence.favorable) :=
  boundary_blocks_rough_adequacy twoEvidenceSpace TwoEvidence.favorable
    twoEvidence_favorable_boundary

example :
    And (UpperApprox twoEvidenceSpace TwoEvidence.favorable)
      (Not (RoughAdequacyEligible twoEvidenceSpace TwoEvidence.favorable)) :=
  upper_not_necessarily_rough_adequacy

example :
    AdequacyProfileBlocked roughBoundaryAdequacyProfile :=
  roughBoundaryAdequacyProfile_blocked

example :
    Not (AdequacyProfileSatisfied roughBoundaryAdequacyProfile) :=
  roughBoundaryAdequacyProfile_not_satisfied

example :
    RoughAdequacyEligible fineTwoEvidenceSpace TwoEvidence.favorable :=
  fineTwoEvidence_favorable_eligible

example :
    Not (BoundaryRegion fineTwoEvidenceSpace TwoEvidence.favorable) :=
  fineTwoEvidence_favorable_not_boundary

example :
    And
      (Not (RoughAdequacyEligible twoEvidenceSpace TwoEvidence.favorable))
      (RoughAdequacyEligible fineTwoEvidenceSpace TwoEvidence.favorable) :=
  granularity_changes_favorable_adequacy

example (item : TwoEvidence)
    (hLower : LowerApprox twoEvidenceSpace item) :
    LowerApprox fineTwoEvidenceSpace item :=
  twoEvidence_coarse_lower_implies_fine_lower item hLower

example :
    And
      (LowerApprox fineTwoEvidenceSpace TwoEvidence.favorable)
      (Not (LowerApprox twoEvidenceSpace TwoEvidence.favorable)) :=
  fine_lower_does_not_imply_coarse_lower

example :
    BoundaryRegion coarseThreeEvidenceSpace ThreeEvidence.favorable :=
  coarseThreeEvidence_favorable_boundary

example (item : ThreeEvidence)
    (hLower : LowerApprox coarseThreeEvidenceSpace item) :
    LowerApprox fineThreeEvidenceSpace item :=
  threeEvidence_coarse_lower_implies_fine_lower item hLower

example :
    And
      (LowerApprox fineThreeEvidenceSpace ThreeEvidence.favorable)
      (Not (LowerApprox coarseThreeEvidenceSpace ThreeEvidence.favorable)) :=
  threeEvidence_favorable_converse_failure

example :
    And
      (LowerApprox fineThreeEvidenceSpace ThreeEvidence.corroborating)
      (Not (LowerApprox coarseThreeEvidenceSpace
        ThreeEvidence.corroborating)) :=
  threeEvidence_corroborating_converse_failure

example :
    allThreeGranularityMasks.length = 64 :=
  allThreeGranularityMasks_length

example :
    ThreeGranularityMask.Refines identityThreeGranularityMask
      allTrueThreeGranularityMask :=
  identityThreeGranularityMask_refines_all_true

example :
    And
      (LowerApprox identityThreeGranularityMask.space
        ThreeEvidence.favorable)
      (Not (LowerApprox allTrueThreeGranularityMask.space
        ThreeEvidence.favorable)) :=
  mask_payload_converse_failure

example :
    AdequacyProfileSatisfied fineAdequacyProfile :=
  fineAdequacyProfile_satisfied

example :
    And
      (EvaluatorAcceptsSem
        evaluatorAcceptedButUndefendedSelection.evaluator
        evaluatorAcceptedButUndefendedSelection.insight)
      (Not (DefendedEvaluatorAcceptance
        evaluatorAcceptedButUndefendedSelection)) :=
  evaluator_acceptance_not_necessarily_defended

example : ScoreAccepts ScoreLevel.high :=
  high_score_accepts

example : Not (ScoreAccepts ScoreLevel.low) :=
  low_score_not_accepts

example :
    ScoreDisagreement ScoreLevel.high ScoreLevel.low :=
  high_low_scores_disagree

example :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.high
        third := ScoreLevel.low } = EvaluationValue.accepts :=
  two_high_one_low_majority_accepts

example :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.low
        third := ScoreLevel.low } = EvaluationValue.rejects :=
  one_high_two_low_majority_rejects

example :
    majorityDecision
      { first := ScoreLevel.high
        second := ScoreLevel.medium
        third := ScoreLevel.medium } = EvaluationValue.abstains :=
  one_high_two_medium_majority_abstains

example :
    AtLeastTwoAccept
      { first := ScoreLevel.high
        second := ScoreLevel.high
        third := ScoreLevel.low } :=
  atLeastTwoAccept_two_high_one_low

example :
    Not (AtLeastTwoAccept
      { first := ScoreLevel.high
        second := ScoreLevel.medium
        third := ScoreLevel.medium }) :=
  not_atLeastTwoAccept_one_high_two_medium

example :
    Not (SatisfactionCondition unitSyntaxTranslation) :=
  unitSyntaxTranslation_not_satisfaction_preserving

example (fragment : LogicFragment) :
    SatisfactionCondition (identityFragmentTranslation fragment) :=
  identityFragmentTranslation_satisfies_condition fragment

example :
    documentedEvidenceConcept.extent EvidenceObject.recordA :=
  documentedEvidenceConcept_extent_contains_recordA

example :
    documentedEvidenceConcept.intent EvidenceAttribute.documented :=
  documentedEvidenceConcept_intent_has_documented

example :
    Not (documentedEvidenceConcept.intent EvidenceAttribute.contested) :=
  documentedEvidenceConcept_intent_not_contested

example :
    ConceptAttributionBlocked contestedDocumentedConceptProfile :=
  contestedDocumentedConceptProfile_blocked

example :
    Not (ConceptAttributionSatisfied contestedDocumentedConceptProfile) :=
  contestedDocumentedConceptProfile_not_satisfied

example :
    ConceptAttributionSatisfied documentedDocumentedConceptProfile :=
  documentedDocumentedConceptProfile_satisfied

end Paralogic
