# Theorem Ledger

All listed entries are encoded in Lean unless marked as future work.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| T-ISF-1 | `ISF -> Uses` | `ISF_to_Uses` |
| T-ISF-2 | `ISF -> Claims` | `ISF_to_Claims` |
| T-ISF-3 | `ISF -> SupportDegraded` | `ISF_to_SupportDegraded` |
| T-ISF-4 | `ISF -> TreatsAsAdequate` | `ISF_to_TreatsAsAdequate` |
| T-M8-1 | `M8 -> ISF` | `M8_to_ISF` |
| T-M8-2 | `M8 -> Uses` | `M8_to_Uses` |
| T-M8-3 | `M8 -> Claims` | `M8_to_Claims` |
| T-VI-1 | `ValidInsight -> CandidateInsight` | `ValidInsight_to_CandidateInsight` |
| T-VI-2 | `ValidInsight -> EvaluatorAccepts` | `ValidInsight_to_EvaluatorAccepts` |
| C-ISF-1 | `Uses not-> ISF` | `ISF_does_not_follow_from_Uses` |
| C-ISF-2 | `Claims not-> ISF` | `ISF_does_not_follow_from_Claims` |
| C-ISF-3 | `SupportDegraded not-> ISF` | `ISF_does_not_follow_from_SupportDegraded` |
| C-ISF-4 | `Uses + Claims + SupportDegraded not-> ISF` | `ISF_needs_TreatsAsAdequate` |
| C-M8-1 | `ISF not-> M8` | `ISF_does_not_imply_M8` |
| C-M8-2 | `M8 not-> Harm` | `M8_does_not_imply_harm` |
| C-M8-3 | `M8 not-> Illegality` | `M8_does_not_imply_illegality` |
| C-M8-4 | `M8 not-> MoralGuilt` | `M8_does_not_imply_moralGuilt` |
| C-EVAL-1 | `EvaluatorAccepts not-> ValidInsight` | `EvaluatorAccepts_does_not_imply_ValidInsight` |
| C-VI-1 | `ValidInsight not-> EmpiricalTruth` | `ValidInsight_does_not_imply_empiricalTruth` |
| C-VI-2 | `ValidInsight not-> Repair` | `ValidInsight_does_not_imply_repair` |
| C-DELTA-1 | `DeltaResolution not-> EmpiricalTruth` | `DeltaResolution_does_not_imply_empiricalTruth` |
| C-EMP-1 | `EmpiricalValidation not-> GovernanceLegitimacy` | `EmpiricalValidation_does_not_imply_governanceLegitimacy` |

## Future Theorem Families

- Many-sorted soundness for the finite kernel embedding.
- Frame morphism preservation and non-preservation theorems.
- Evaluator soundness relative to explicit criteria.
- Delta outcome exclusivity or overlap theorems.
- Repair calculus non-collapse theorems.
- Normative bridge soundness and non-entailment theorems.
- Empirical validation boundary theorems.

## Many-Sorted Model Semantics Ledger

Status: MC3-Lean for the encoded statements included in the successful local
Lean build recorded on 2026-06-07.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| MS-M8-1 | `M8Sem -> ISFSem` | `M8Sem_to_ISFSem` |
| MS-VI-1 | `ValidInsightSem -> EvaluatorAcceptsSem` | `ValidInsightSem_to_EvaluatorAccepts` |
| MS-C-M8-1 | `M8Sem not-> HarmBridgeSem` | `m8Only_is_M8Sem`, `m8Only_not_harmBridge` |
| MS-C-M8-2 | `M8Sem not-> MoralGuiltBridgeSem` | `m8Only_is_M8Sem`, `m8Only_not_moralGuiltBridge` |
| MS-C-M8-3 | `M8Sem not-> RepairObligationBridgeSem` | `m8Only_is_M8Sem`, `m8Only_not_repairObligationBridge` |
| MS-C-EVAL-1 | `EvaluatorAcceptsSem not-> ValidInsightSem` | `evaluatorOnly_accepts_sem`, `evaluatorOnly_not_ValidInsightSem` |
| MS-C-VI-1 | `ValidInsightSem not-> FullEmpiricalValidationSem` | `validInsightOnly_is_ValidInsightSem`, `validInsightOnly_not_FullEmpiricalValidationSem` |
| MS-C-EMP-1 | `EmpiricalValidationSem not-> FullEmpiricalValidationSem` | `empiricalNominal_has_EmpiricalValidationSem`, `empiricalNominal_not_FullEmpiricalValidationSem` |
| MS-PRES-1 | model homomorphisms preserve `UsesSem` | `ModelHom_preserves_UsesSem` |
| MS-PRES-2 | model homomorphisms preserve `ClaimsSem` | `ModelHom_preserves_ClaimsSem` |
| MS-PRES-3 | model homomorphisms preserve `ISFSem` | `ModelHom_preserves_ISFSem` |
| MS-PRES-4 | model homomorphisms preserve `ValidInsightSem` | `ModelHom_preserves_ValidInsightSem` |
| MS-PRES-5 | model-hom composition is pointwise associative on carrier maps | `composeModelHom_assoc_map` |
| MS-PRES-6 | model homomorphisms preserve term evaluation under mapped assignments | `ModelHom_preserves_evalTerm` |
| MS-PRES-7 | model homomorphisms preserve argument-list evaluation under mapped assignments | `ModelHom_preserves_evalArgs` |
| MS-PRES-8 | model homomorphisms preserve positive quantifier-free formula satisfaction | `ModelHom_preserves_positive_quantifier_free_satisfaction` |
| MS-NP-1 | model homomorphisms need not preserve negation | `model_hom_not_preserve_negation_counterexample` |
| MS-NP-2 | model homomorphisms need not preserve implication | `model_hom_not_preserve_implication_counterexample` |
| MS-NP-3 | model homomorphisms need not preserve universal quantification | `model_hom_not_preserve_universal_counterexample` |
| MS-ISO-1 | argument-list maps respect pointwise left inverses | `args_map_left_inverse` |
| MS-ISO-2 | model isomorphisms are forward/backward model homomorphisms with pointwise inverses | `ModelIso` |
| MS-ISO-3 | every model has an identity model isomorphism | `identityModelIso` |
| MS-ISO-4 | model isomorphisms compose | `composeModelIso` |
| MS-ISO-5 | composed model-isomorphism forward map is pointwise composition | `composeModelIso_forward_map` |
| MS-ISO-6 | model isomorphisms reflect predicate satisfaction | `ModelIso_reflectsPredicate` |
| MS-ISO-7 | model isomorphisms preserve and reflect positive quantifier-free formula satisfaction | `ModelIso_positive_quantifier_free_satisfaction_iff` |
| MS-ISO-8 | model isomorphisms transport assignment updates along inverse carrier maps | `ModelIso_forward_updateAssignment`, `ModelIso_forward_updateAssignment_source`, `ModelIso_backward_updateAssignment` |
| MS-ISO-9 | model isomorphisms preserve and reflect full formula satisfaction | `ModelIso_full_formula_satisfaction_iff` |
| MS-TRANS-1 | formula translations preserve satisfied premise lists | `FormulaTranslation_preserves_satisfies_all` |
| MS-TRANS-2 | identity formula translation preserves formulas definitionally | `identityFormulaTranslation_apply` |
| MS-TRANS-3 | composed formula translation applies translations in sequence | `composeFormulaTranslation_apply` |
| MS-TRANS-4 | satisfaction-preserving formula translations transport a source instance of semantic entailment | `FormulaTranslation_transports_semantic_entailment_instance` |
| NB-1 | applicable normative bridge schema warrants its conclusion | `NormativeBridgeSchema_to_conclusion` |
| NB-2 | missing bridge premise blocks application | `missing_premise_blocks_bridge` |
| NB-3 | bridge scope failure blocks application | `scope_failure_blocks_bridge` |
| NB-4 | bridge defeater blocks application | `defeater_blocks_bridge` |
| EMP-PROT-1 | applicable empirical protocol warrants full validation | `EmpiricalValidationProtocol_to_full_validation` |
| EMP-PROT-2 | no operationalization blocks empirical protocol | `no_operationalization_blocks_empirical_protocol` |
| EMP-PROT-3 | no construct validity blocks empirical protocol | `no_construct_validity_blocks_empirical_protocol` |
| EMP-PROT-4 | no reliability testing blocks empirical protocol | `no_reliability_blocks_empirical_protocol` |
| EMP-PROT-5 | no replication blocks empirical protocol | `no_replication_blocks_empirical_protocol` |
| FIN-VAL-1 | true valuation makes interpreted predicate true | `finitePredicateModel_predicate_true` |
| FIN-VAL-2 | false valuation makes interpreted predicate false | `finitePredicateModel_predicate_false` |
| ADEQ-1 | satisfied adequacy profile warrants `adequate` predicate | `AdequacyProfile_to_AdequateSem` |
| ADEQ-2 | irrelevance blocks adequacy profile | `irrelevance_blocks_adequacy` |
| ADEQ-3 | insufficiency blocks adequacy profile | `insufficiency_blocks_adequacy` |
| ADEQ-4 | stale support blocks adequacy profile | `stale_support_blocks_adequacy` |
| ADEQ-5 | methodological mismatch blocks adequacy profile | `method_mismatch_blocks_adequacy` |
| ADEQ-6 | unbounded uncertainty blocks adequacy profile | `unbounded_uncertainty_blocks_adequacy` |
| ADEQ-7 | scope mismatch blocks adequacy profile | `scope_mismatch_blocks_adequacy` |
| EVAL-CRIT-1 | satisfied evaluator criteria warrant acceptance | `EvaluatorCriteria_to_accepts` |
| EVAL-CRIT-2 | missing criteria declaration blocks acceptance schema | `missing_criteria_declaration_blocks_acceptance` |
| EVAL-CRIT-3 | irrelevant criteria block acceptance schema | `irrelevant_criteria_blocks_acceptance` |
| EVAL-CRIT-4 | uninspected evidence blocks acceptance schema | `uninspected_evidence_blocks_acceptance` |
| EVAL-CRIT-5 | unapplied criteria block acceptance schema | `unapplied_criteria_blocks_acceptance` |
| EVAL-CRIT-6 | evaluation error blocks acceptance schema | `evaluation_error_blocks_acceptance` |
| EVAL-SOUND-1 | criteria-relative soundness yields only its declared conclusion | `criteria_relative_soundness_to_conclusion` |
| M8P-1 | satisfied power profile warrants power relevance | `PowerConditionProfile_to_powerRelevant` |
| M8P-2 | satisfied power profile warrants power validity dependence | `PowerConditionProfile_to_powerValidityDependence` |
| M8P-3 | satisfied power profile warrants power omission | `PowerConditionProfile_to_powerOmitted` |
| M8P-4 | satisfied M8 power-erasure case warrants `M8Sem` | `M8PowerErasureCase_to_M8Sem` |
| M8P-BLOCK-1 | irrelevant power blocks profile | `irrelevant_power_blocks_profile` |
| M8P-BLOCK-2 | represented power blocks profile | `represented_power_blocks_profile` |
| M8P-BLOCK-3 | immaterial omission blocks profile | `immaterial_omission_blocks_profile` |
| M8P-BLOCK-4 | immaterial affected group blocks profile | `immaterial_affected_group_blocks_profile` |
| M8P-BLOCK-5 | disclosed power blocks profile | `disclosed_power_blocks_profile` |
| M8P-BLOCK-6 | mitigated power blocks profile | `mitigated_power_blocks_profile` |

## Gate 1 Foundation Lemmas

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G1-SUBST-1 | identity substitution preserves terms | `substTerm_identity` |
| G1-SUBST-2 | identity substitution preserves typed argument lists | `substArgs_identity` |
| G1-SAT-1 | truth is always satisfied | `satisfies_truth` |
| G1-SAT-2 | falsity is never satisfied | `not_satisfies_falsity` |
| G1-SAT-3 | conjunction introduction | `satisfies_conj_intro` |
| G1-SAT-4 | conjunction left elimination | `satisfies_conj_left` |
| G1-SAT-5 | conjunction right elimination | `satisfies_conj_right` |
| G1-SAT-6 | disjunction left introduction | `satisfies_disj_left` |
| G1-SAT-7 | disjunction right introduction | `satisfies_disj_right` |
| G1-SAT-8 | implication elimination | `satisfies_impl_elim` |
| G1-SAT-9 | universal elimination | `satisfies_forall_elim` |
| G1-SAT-10 | existential introduction | `satisfies_exists_intro` |
| G1-ALL-1 | empty premise list is satisfied | `satisfies_all_nil` |
| G1-ALL-2 | premise-list cons introduction | `satisfies_all_cons_intro` |
| G1-ALL-3 | premise-list head elimination | `satisfies_all_cons_head` |
| G1-ALL-4 | premise-list tail elimination | `satisfies_all_cons_tail` |
| G1-ENT-1 | semantic entailment reflexivity | `semantically_entails_refl` |
| G1-ENT-2 | truth is semantically entailed by any premise list | `semantically_entails_truth` |
| G1-ENT-3 | semantic entailment transitivity through singleton middle premise | `semantically_entails_trans` |
| G1-AGR-1 | assignment agreement on a term preserves term evaluation | `evalTerm_eq_of_agree` |
| G1-AGR-2 | assignment agreement on typed arguments preserves argument evaluation | `evalArgs_eq_of_agree` |
| G1-AGR-3 | assignment agreement on a formula preserves satisfaction | `satisfiesFormula_iff_of_agree` |
| G1-CAP-1 | masking identity substitution leaves identity substitution unchanged | `maskSubstitution_identity` |
| G1-CAP-2 | a universal binder binds its own variable | `quantified_variable_not_free_forall` |
| G1-CAP-3 | an existential binder binds its own variable | `quantified_variable_not_free_exists` |
| G1-SUBST-3 | identity substitution preserves formulas | `substFormula_identity` |
| G1-SUBST-4 | term substitution commutes with evaluation via substitution assignment | `evalTerm_subst` |
| G1-SUBST-5 | typed-argument substitution commutes with evaluation via substitution assignment | `evalArgs_subst` |
| G1-SUBST-6 | quantifier-free substitution/satisfaction interaction | `satisfies_subst_iff_quantifier_free` |
| G1-ALL-5 | append-left premise satisfaction projection | `satisfies_all_append_left` |
| G1-ALL-6 | append-right premise satisfaction projection | `satisfies_all_append_right` |
| G1-ALL-7 | append premise satisfaction introduction | `satisfies_all_append_intro` |
| G1-ENT-4 | semantic entailment monotone under right premise extension | `semantically_entails_append_monotone_right` |
| G1-ENT-5 | semantic entailment monotone under left premise extension | `semantically_entails_append_monotone_left` |

## Gate 1B Proof-Theory Soundness Fragment

Status: MC3-Lean plus PPC-bounded executable checking for a deliberately
scoped propositional derivability calculus.  This is not a completeness theorem
and not a full quantified natural-deduction system.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G1B-DER-1 | satisfied premise lists satisfy every listed premise | `satisfies_all_mem` |
| G1B-DER-2 | derivability implies semantic entailment for the encoded calculus | `derives_sound` |
| G1B-DER-3 | semantic countermodels block semantic entailment | `semantic_countermodel_blocks_entailment` |
| G1B-DER-4 | failed semantic entailment has a semantic countermodel, classically | `not_entails_has_countermodel` |
| G1B-DER-5 | derivability in the sound fragment rules out semantic countermodels | `derives_no_countermodel` |
| G1B-DER-6 | conjunction-left derivation example is sound | `derives_conj_left_example_sound` |
| G1B-DER-7 | implication-elimination derivation example is sound | `derives_modus_ponens_example_sound` |
| G1B-DER-8 | implication-introduction derivation example is sound | `derives_implication_intro_example_sound` |
| G1B-DER-9 | falsity-elimination derivation example is sound | `derives_falsity_elim_example_sound` |
| G1B-DER-10 | disjunction-elimination derivation example is sound | `derives_disj_elim_example_sound` |
| G1B-DER-11 | derivability is monotone under appending extra premises on the right | `derives_append_monotone_right` |
| G1B-DER-12 | right-weakened derivations are semantically sound | `derives_append_monotone_right_sound` |
| G1B-SEM-Q1 | universal current-value elimination is semantically valid | `semantically_entails_forall_current` |
| G1B-SEM-Q2 | existential current-value introduction is semantically valid | `semantically_entails_exists_current` |

## Gate K Contextual Obstruction Semantics

Status: MC3-Lean exploratory core.  This is a real checked mathematical layer,
not a completed ISFT specialization.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| GK-CTX-1 | global extension blocks contextual obstruction | `global_extension_not_obstructed` |
| GK-CTX-2 | contextual obstruction blocks global extension | `obstruction_blocks_extension` |
| GK-CTX-3 | jointly monic covers make global extensions unique | `jointly_monic_global_extension_unique` |
| GK-CTX-4 | a two-projection Boolean cover has a global extension | `boolPairFamily_has_global_extension` |
| GK-CTX-5 | the Boolean-pair cover is jointly monic | `BoolPairPresheaf_jointly_monic` |
| GK-CTX-6 | an empty-root local family has a contextual obstruction | `noGlobalFamily_obstructed` |
| GK-DELTA-1 | one Delta step preserves reachability | `delta_step_preserves_reachability` |
| GK-DELTA-2 | stable states block non-self transitions | `stable_blocks_nonself_step` |
| GK-DELTA-3 | a two-state Delta system reaches resolution | `twoDelta_eventually_resolution` |
| GK-DELTA-4 | the repaired state in the two-state system is stable | `twoDelta_repaired_stable` |
| GK-DELTA-5 | the start state in the two-state system is not stable | `twoDelta_start_not_stable` |
| GK-DELTA-6 | a one-state iterative loop does not eventually reach resolution | `loopDelta_not_eventually_resolution` |
| GK-DELTA-7 | the start state in the two-state system is reachable | `twoDelta_start_reachable` |
| GK-DELTA-8 | eventual Delta resolution does not imply global Delta finality | `eventual_resolution_not_global_finality` |
| GK-DELTA-9 | stable resolution implies eventual resolution | `stable_resolution_implies_eventual_resolution` |
| GK-DELTA-10 | the two-state Delta system reaches stable resolution | `twoDelta_eventually_stable_resolution` |
| GK-DELTA-11 | stable resolution does not imply global finality | `stable_resolution_not_global_finality` |
| GK-DELTA-12 | the one-state iterative loop is stable | `loopDelta_stable`, `loopDelta_eventually_stable` |
| GK-DELTA-13 | eventual stability does not imply eventual resolution | `eventual_stability_not_eventual_resolution` |
| GK-DELTA-14 | always over reachable states implies eventually over reachable states | `delta_always_implies_eventually` |
| GK-DELTA-15 | eventual resolution and global finality match modal eventually/always resolution predicates | `eventual_resolution_iff_eventually_resolution_state`, `global_finality_iff_always_resolution` |
| GK-DELTA-16 | modal eventual resolution does not imply modal always resolution | `eventual_not_always_resolution_modal` |
| GK-DELTA-17 | modal eventual stability does not imply modal eventual resolution | `eventual_stability_not_eventual_resolution_modal` |
| GK-DELTA-18 | reachable states form a transition-closed predicate | `delta_reachable_closed` |
| GK-DELTA-19 | reachable states are contained in every transition-closed predicate containing the initial state | `delta_reachable_least_closed` |
| GK-DELTA-20 | the all-state predicate is closed for the two-state Delta system | `twoDelta_all_states_closed` |
| GK-DELTA-21 | the start-only predicate is not closed for the two-state Delta system | `twoDelta_start_only_not_closed` |
| GK-DELTA-22 | every closed predicate over the two-state Delta system contains the repaired state | `twoDelta_repaired_in_every_closed` |
| GK-REPAIR-1 | unique minimal repair implies existence of a minimal repair | `unique_minimal_implies_minimal` |
| GK-REPAIR-1B | a best acceptable state in an antisymmetric preference frame is the unique minimal repair | `best_acceptable_unique_minimal` |
| GK-REPAIR-2 | a two-choice repair frame has a minimal repair | `twoRepair_has_minimal` |
| GK-REPAIR-3 | the two-choice repair frame does not have a unique minimal repair | `twoRepair_not_unique_minimal` |
| GK-REPAIR-4 | the ranked repair frame has a minimal repair | `rankedRepair_has_minimal` |
| GK-REPAIR-5 | the ranked repair frame has a unique minimal acceptable repair | `rankedRepair_has_unique_minimal` |
| GK-REPAIR-5B | the ranked repair frame instantiates the best-acceptable unique-minimal theorem | `rankedRepair_unique_minimal_from_best` |
| GK-REPAIR-6 | targeted repair satisfies success, minimality, and conservatism | `targetedRepair_satisfies_revision_postulates` |
| GK-REPAIR-7 | partial repair fails success | `partialRepair_not_successful` |
| GK-REPAIR-8 | no-action repair fails success | `doNothingRepair_not_successful` |
| GK-REPAIR-9 | excessive repair succeeds weakly but is not minimal | `excessiveRepair_successful_not_minimal` |
| GK-REPAIR-10 | excessive repair fails the full revision-postulate package | `excessiveRepair_not_revision_postulates` |
| GK-REPAIR-11 | diagnosis-guided targeted repair warrants the supplied repair-obligation bridge | `repairBridgeOnlyTargetedRevision_warrants_obligation` |
| GK-REPAIR-12 | adequate action satisfies the independence-frame postulate package | `adequateAction_satisfies_independence_package` |
| GK-REPAIR-13 | redundant action satisfies success and conservatism but fails minimality | `redundantAction_success_conservative_not_minimal` |
| GK-REPAIR-14 | overreach action satisfies success and minimality but fails conservatism | `overreachAction_success_minimal_not_conservative` |
| GK-REPAIR-15 | failed action satisfies conservatism but fails success | `failedAction_conservative_not_successful` |
| GK-ARG-1 | admissibility implies conflict-freeness | `admissible_is_conflict_free` |
| GK-ARG-2 | admissibility defends every selected argument | `admissible_defends_selected` |
| GK-ARG-3 | target-only selection is conflict-free in a two-argument attack frame | `targetOnly_conflict_free` |
| GK-ARG-4 | target-only selection is not defended | `targetOnly_not_defended` |
| GK-ARG-5 | target-only selection is not admissible | `targetOnly_not_admissible` |
| GK-ARG-6 | the empty selection is admissible in any argumentation framework | `emptySelection_admissible` |
| GK-ARG-7 | defended evaluator acceptance implies evaluator acceptance | `defended_acceptance_implies_evaluator_accepts` |
| GK-ARG-8 | defended evaluator acceptance implies admissibility | `defended_acceptance_implies_admissible` |
| GK-ARG-9 | evaluator acceptance alone need not be defended acceptance | `evaluator_acceptance_not_necessarily_defended` |
| GK-ROUGH-1 | lower approximation implies upper approximation | `lower_implies_upper` |
| GK-ROUGH-2 | boundary region implies possible support | `boundary_implies_possible` |
| GK-ROUGH-3 | boundary region blocks definite support | `boundary_not_definite` |
| GK-ROUGH-4 | favorable item is boundary-level under coarse indiscernibility | `twoEvidence_favorable_boundary` |
| GK-ROUGH-5 | unfavorable item is boundary-level under coarse indiscernibility | `twoEvidence_unfavorable_boundary` |
| GK-ROUGH-6 | boundary status blocks rough adequacy eligibility | `boundary_blocks_rough_adequacy` |
| GK-ROUGH-7 | upper approximation alone does not entail rough adequacy eligibility | `upper_not_necessarily_rough_adequacy` |
| GK-ROUGH-8 | profile sufficiency linked to rough lower approximation yields lower approximation | `rough_lower_from_profile_sufficient` |
| GK-ROUGH-9 | rough lower approximation yields linked profile sufficiency | `profile_sufficient_from_rough_lower` |
| GK-ROUGH-10 | boundary evidence blocks linked adequacy-profile satisfaction | `rough_boundary_blocks_profile_satisfaction` |
| GK-ROUGH-11 | boundary evidence blocks linked adequacy profile | `rough_boundary_blocks_profile` |
| GK-ROUGH-12 | concrete rough-boundary adequacy profile is blocked and unsatisfied | `roughBoundaryAdequacyProfile_blocked`, `roughBoundaryAdequacyProfile_not_satisfied` |
| GK-ROUGH-13 | lower approximation is preserved when the evidence relation is refined | `lower_preserved_under_relation_refinement` |
| GK-ROUGH-14 | fine two-item evidence granularity makes favorable evidence lower-approximate and non-boundary | `fineTwoEvidence_favorable_lower`, `fineTwoEvidence_favorable_not_boundary` |
| GK-ROUGH-15 | changing from coarse to fine two-item granularity changes favorable rough adequacy eligibility | `granularity_changes_favorable_adequacy` |
| GK-ROUGH-16 | fine lower approximation need not imply coarse lower approximation | `fine_lower_does_not_imply_coarse_lower` |
| GK-ROUGH-17 | three-item coarse granularity has favorable boundary evidence | `coarseThreeEvidence_favorable_boundary` |
| GK-ROUGH-18 | three-item coarse lower approximation is preserved under identity refinement | `threeEvidence_coarse_lower_implies_fine_lower` |
| GK-ROUGH-19 | three-item fine lower approximation need not imply coarse lower approximation | `threeEvidence_favorable_converse_failure`, `threeEvidence_corroborating_converse_failure` |
| GK-ROUGH-20 | three-item granularity mask enumeration has 64 mask records | `allThreeGranularityMasks_length` |
| GK-ROUGH-21 | identity mask refines the all-true mask | `identityThreeGranularityMask_refines_all_true` |
| GK-ROUGH-22 | mask-level payload witness shows fine lower approximation need not imply coarse lower approximation | `mask_payload_converse_failure` |
| GK-ROUGH-23 | fine-granularity adequacy profile is satisfied and warrants adequacy in its model | `fineAdequacyProfile_satisfied`, `fineAdequacyProfile_to_adequate` |
| GK-FCA-1 | predicate-set equivalence is symmetric | `predEquivalent_symm` |
| GK-FCA-2 | extent-to-intent and intent-to-extent form a Galois connection | `formal_context_galois` |
| GK-FCA-3 | object extents expand under double derivation | `extent_expands_under_double_derivation` |
| GK-FCA-4 | attribute intents expand under double derivation | `intent_expands_under_double_derivation` |
| GK-FCA-5 | all-evidence example has documented-only intent | `allEvidence_intent_is_documented_only` |
| GK-FCA-6 | documented-only intent has all evidence as extent | `documented_only_extent_is_all_evidence` |
| GK-FCA-7 | documented evidence concept includes record A and excludes contested intent | `documentedEvidenceConcept_extent_contains_recordA`, `documentedEvidenceConcept_intent_not_contested` |
| GK-FCA-M7-1 | non-M7 mechanism labels block concept-attribution satisfaction | `non_M7_blocks_concept_attribution` |
| GK-FCA-M7-2 | missing concept intent blocks concept-attribution satisfaction | `missing_intent_blocks_concept_attribution` |
| GK-FCA-M7-3 | satisfied concept-attribution profiles warrant the attributed concept intent | `concept_attribution_satisfied_intent` |
| GK-FCA-M7-4 | contested attribute is blocked for the documented evidence concept | `contestedDocumentedConceptProfile_blocked`, `contestedDocumentedConceptProfile_not_satisfied` |
| GK-FCA-M7-5 | documented attribute satisfies the documented evidence concept profile | `documentedDocumentedConceptProfile_satisfied` |
| GK-INST-1 | satisfaction condition transports target satisfaction to source satisfaction | `satisfaction_condition_forward` |
| GK-INST-2 | satisfaction condition transports source satisfaction to target satisfaction | `satisfaction_condition_backward` |
| GK-INST-3 | a unit syntax translation from true to false fragment is not satisfaction-preserving | `unitSyntaxTranslation_not_satisfaction_preserving` |
| GK-INST-4 | identity fragment translation satisfies the satisfaction condition | `identityFragmentTranslation_satisfies_condition` |

## Gate 2 Model-Theory Lemmas

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G2-ARGS-1 | typed argument-list maps compose | `Args.map_comp` |
| G2-HOM-1 | model homomorphisms compose | `composeModelHom` |
| G2-HOM-2 | composed model homomorphism map is pointwise composition | `composeModelHom_map` |
| G2-HOM-3 | left identity law for model-hom maps | `composeModelHom_identity_left_map` |
| G2-HOM-4 | right identity law for model-hom maps | `composeModelHom_identity_right_map` |
| G2-ISO-1 | model isomorphisms compose and have identity instances | `identityModelIso`, `composeModelIso`, `composeModelIso_forward_map` |
| G2-ISO-2 | model isomorphisms transport assignment updates across inverse maps | `ModelIso_forward_updateAssignment`, `ModelIso_forward_updateAssignment_source`, `ModelIso_backward_updateAssignment` |
| G2-ISO-3 | model isomorphisms preserve and reflect full formula satisfaction | `ModelIso_full_formula_satisfaction_iff` |
| G2-FCM-1 | frame/context morphisms compose | `composeFrameContextMorphism` |
| G2-FCM-2 | composed frame/context morphism map is pointwise composition | `composeFrameContextMorphism_map` |
| G2-TR-1 | formula translations preserve satisfaction of all premises | `FormulaTranslation_preserves_satisfies_all` |
| G2-TR-2 | identity formula translation is definitionally identity on formulas | `identityFormulaTranslation_apply` |
| G2-TR-3 | formula translations compose on formulas | `composeFormulaTranslation_apply` |
| G2-EMB-1 | one-object `World` uses corresponds to many-sorted `UsesSem` | `world_uses_iff_UsesSem` |
| G2-EMB-2 | one-object `World` claims corresponds to many-sorted `ClaimsSem` | `world_claims_iff_ClaimsSem` |
| G2-EMB-3 | one-object support degradation corresponds to `SupportDegradedSem` | `world_supportDegraded_iff_SupportDegradedSem` |
| G2-EMB-4 | one-object treatment corresponds to `TreatsAsAdequateSem` | `world_treatsAsAdequate_iff_TreatsAsAdequateSem` |
| G2-EMB-5 | old `ISF` embeds into `ISFSem` | `world_ISF_to_ISFSem` |
| G2-EMB-6 | old `M8` embeds into `M8Sem` | `world_M8_to_M8Sem` |
| G2-EMB-7 | old `ValidInsight` embeds into `ValidInsightSem` | `world_ValidInsight_to_ValidInsightSem` |
| G2-EMB-C1 | old M8 no-bridge witness embeds as no harm bridge | `world_m8NoBridge_not_HarmBridgeSem` |
| G2-EMB-C2 | old M8 no-bridge witness embeds as no moral-guilt bridge | `world_m8NoBridge_not_MoralGuiltBridgeSem` |
| G2-EMB-C3 | old M8 no-bridge witness embeds as no repair-obligation bridge | `world_m8NoBridge_not_RepairObligationBridgeSem` |
| G2-EMB-C4 | old evaluator-only witness embeds as not `ValidInsightSem` | `world_evaluatorOnly_not_ValidInsightSem` |
| G2-EMB-C5 | old valid-insight no-bridge witness embeds as not full empirical validation | `world_validInsightNoBridge_not_FullEmpiricalValidationSem` |
| G2-MS-C1 | independent many-sorted `UsesSem` does not imply `ISFSem` | `usesOnlySemantic_has_UsesSem`, `usesOnlySemantic_not_ISFSem` |
| G2-MS-C2 | independent many-sorted `ClaimsSem` does not imply `ISFSem` | `claimsOnlySemantic_has_ClaimsSem`, `claimsOnlySemantic_not_ISFSem` |
| G2-MS-C3 | independent many-sorted `SupportDegradedSem` does not imply `ISFSem` | `supportOnlySemantic_has_SupportDegradedSem`, `supportOnlySemantic_not_ISFSem` |
| G2-MS-C4 | uses plus claims plus support degradation do not imply `ISFSem` without treatment | `noTreatmentSemantic_has_uses_claims_support`, `noTreatmentSemantic_not_ISFSem` |
| G2-MS-C5 | independent many-sorted `ISFSem` does not imply `M8Sem` | `isfNotM8Semantic_is_ISFSem`, `isfNotM8Semantic_not_M8Sem` |
| G2-MS-C6 | contradiction presence does not imply `ValidInsightSem` | `deltaOnlySemantic_not_ValidInsightSem` |
| G2-NP-1 | source `UsesSem` may fail to preserve under a mere sort map | `erasingSortMap_source_has_UsesSem`, `erasingSortMap_target_not_UsesSem` |
| G2-NP-2 | erasing sort map is not a model homomorphism | `erasingSortMap_not_ModelHom` |
| G2-NP-3 | model homomorphism preservation fails for negation | `model_hom_not_preserve_negation_counterexample` |
| G2-NP-4 | model homomorphism preservation fails for implication | `model_hom_not_preserve_implication_counterexample` |
| G2-NP-5 | model homomorphism preservation fails for universal quantification | `model_hom_not_preserve_universal_counterexample` |
| G2-FIN-1 | lack of finite witness record is not an infinitude theorem | `no_finite_witness_is_not_infinitude_claim` |
| G2-FIN-2 | missing machine-readable witness blocks finite-check coverage | `missing_machine_witness_blocks_coverage` |
| G2-FIN-3 | wrong witness expectation blocks finite-check coverage | `wrong_witness_expectation_blocks_coverage` |
| G2-FIN-4 | satisfied coverage record has expected witness flag | `coverage_record_satisfied_not_incomplete_by_witness_flag` |
| G2-SIG-1 | function-symbol enumeration length matches core signature count | `allFunctionSymbols_length` |
| G2-SIG-2 | predicate-symbol enumeration length matches core signature count | `allPredicateSymbols_length` |
| G2-SIG-3 | every function symbol appears in the finite-model enumeration | `allFunctionSymbols_complete` |
| G2-SIG-4 | every predicate symbol appears in the finite-model enumeration | `allPredicateSymbols_complete` |
| G2-SIG-5 | function-symbol enumeration has no duplicates | `allFunctionSymbols_nodup` |
| G2-SIG-6 | predicate-symbol enumeration has no duplicates | `allPredicateSymbols_nodup` |
| G2-BOOL-1 | each sort in the Bool-carrier finite model has two listed elements | `boolFiniteSortWitness_has_two_elements` |
| G2-BOOL-2 | two-element uses-only model satisfies `UsesSem` | `twoUsesOnly_has_UsesSem` |
| G2-BOOL-3 | two-element uses-only model does not satisfy `ISFSem` | `twoUsesOnly_not_ISFSem` |
| G2-BOOL-4 | two-element ISF-not-M8 model satisfies `ISFSem` | `twoISFNotM8_is_ISFSem` |
| G2-BOOL-5 | two-element ISF-not-M8 model does not satisfy `M8Sem` | `twoISFNotM8_not_M8Sem` |

## Gate 3 Contradiction Calculus

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G3-CON-1 | contradiction case entails contradiction presence | `ContradictionCase_to_present` |
| G3-CON-2 | logical contradiction case entails contradiction presence | `logical_case_to_present` |
| G3-CON-3 | semantic contradiction case entails contradiction presence | `semantic_case_to_present` |
| G3-CON-4 | support-treatment contradiction case entails contradiction presence | `support_treatment_case_to_present` |
| G3-NC-1 | contradiction presence does not imply `ValidInsightSem` | `contradictionOnly_has_contradiction`, `contradictionOnly_not_ValidInsightSem` |
| G3-NC-2 | contradiction presence does not imply full empirical validation | `contradictionOnly_has_contradiction`, `contradictionOnly_not_FullEmpiricalValidationSem` |
| G3-NC-3 | contradiction presence does not imply harm bridge | `contradictionOnly_has_contradiction`, `contradictionOnly_not_HarmBridgeSem` |
| G3-NC-4 | contradiction presence does not imply moral-guilt bridge | `contradictionOnly_has_contradiction`, `contradictionOnly_not_MoralGuiltBridgeSem` |
| G3-NC-5 | contradiction presence does not imply repair-obligation bridge | `contradictionOnly_has_contradiction`, `contradictionOnly_not_RepairObligationBridgeSem` |
| G3-NC-6 | contradiction presence does not imply directional frame change | `contradictionNoCollapse_has_contradiction`, `contradictionNoCollapse_not_directional_change` |
| G3-PROF-1 | satisfied contradiction profile yields contradiction case | `ContradictionProfile.toCase` |
| G3-PROF-2 | domain failure blocks contradiction profile | `contradiction_domain_failure_blocks_profile` |
| G3-PROF-3 | no incompatibility blocks contradiction profile | `no_incompatibility_blocks_profile` |
| G3-PROF-4 | scope mismatch blocks contradiction profile | `scope_mismatch_blocks_contradiction_profile` |
| G3-PROF-5 | context mismatch blocks contradiction profile | `context_mismatch_blocks_contradiction_profile` |
| G3-PROF-6 | resolved status blocks contradiction profile | `resolved_status_blocks_contradiction_profile` |
| G3-PROF-7 | logical profile yields logical case | `logical_profile_to_case` |
| G3-PROF-8 | semantic profile yields semantic case | `semantic_profile_to_case` |
| G3-PROF-9 | support-treatment profile yields support-treatment case | `support_treatment_profile_to_case` |
| G3-PROF-10 | pragmatic profile yields pragmatic case | `pragmatic_profile_to_case` |
| G3-PROF-11 | normative profile yields normative case | `normative_profile_to_case` |
| G3-PROF-12 | institutional profile yields institutional case | `institutional_profile_to_case` |
| G3-PROF-13 | frame-conflict profile yields frame-conflict case | `frame_conflict_profile_to_case` |
| G3-PROF-14 | symbolic profile yields symbolic case | `symbolic_profile_to_case` |
| G3-PROF-15 | sacred profile yields sacred case | `sacred_profile_to_case` |
| G3-PROF-16 | residue profile yields residue case | `residue_profile_to_case` |
| G3-PROF-17 | contradiction-only profile is satisfied for any kind | `contradictionOnlyProfile_satisfied` |
| G3-NC-7 | satisfied contradiction profile need not imply valid insight | `satisfied_profile_not_necessarily_valid_insight` |
| G3-NC-8 | satisfied contradiction profile need not imply empirical validation | `satisfied_profile_not_necessarily_empirical_validation` |
| G3-NC-9 | satisfied contradiction profile need not imply moral guilt | `satisfied_profile_not_necessarily_moral_guilt` |

## Gate 4 Insight And Delta Calculus

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G4-DELTA-BLOCK-1 | missing transition blocks Delta outcome | `no_transition_blocks_delta` |
| G4-DELTA-BLOCK-2 | unprocessed contradiction blocks Delta outcome | `unprocessed_contradiction_blocks_delta` |
| G4-DELTA-BLOCK-3 | no evaluator classification blocks Delta outcome | `no_evaluator_classification_blocks_delta` |
| G4-DELTA-1 | Delta resolution-only case is satisfied | `deltaResolutionOnly_satisfied` |
| G4-NC-1 | Delta resolution does not imply full empirical validation | `deltaResolution_not_FullEmpiricalValidation` |
| G4-NC-2 | Delta resolution does not imply harm bridge | `deltaResolution_not_HarmBridge` |
| G4-NC-3 | Delta resolution does not imply repair-obligation bridge | `deltaResolution_not_RepairObligationBridge` |
| G4-NC-4 | false insight does not imply `ValidInsightSem` | `falseInsight_not_ValidInsightSem` |
| G4-NC-5 | null insight does not imply `ValidInsightSem` | `nullInsight_not_ValidInsightSem` |
| G4-POL-1 | exclusive Delta compatibility implies equal outcomes | `exclusive_delta_compatibility_eq` |
| G4-POL-2 | overlap-allowed Delta policy is trivially compatible | `overlap_delta_compatibility_trivial` |
| G4-POL-3 | resolution and collapse are incompatible under exclusive policy | `resolution_not_collapse_under_exclusive_policy` |
| G4-POL-4 | false insight and resolution are incompatible under exclusive policy | `falseInsight_not_resolution_under_exclusive_policy` |
| G4-CASE-1 | Delta shift-only case is satisfied | `deltaShiftOnly_satisfied` |
| G4-CASE-2 | Delta collapse-only case is satisfied | `deltaCollapseOnly_satisfied` |
| G4-CASE-3 | Delta iterative-only case is satisfied | `deltaIterativeOnly_satisfied` |
| G4-CASE-4 | Delta null-only case is satisfied | `deltaNullOnly_satisfied` |
| G4-CASE-5 | Delta false-insight-only case is satisfied | `deltaFalseInsightOnly_satisfied` |
| G4-CASE-6 | Delta degenerate-only case is satisfied | `deltaDegenerateOnly_satisfied` |
| G4-NC-6 | Delta shift does not imply full empirical validation | `deltaShift_not_FullEmpiricalValidation` |
| G4-NC-7 | Delta collapse does not imply moral-guilt bridge | `deltaCollapse_not_MoralGuiltBridge` |
| G4-NC-8 | Delta iterative does not imply repair-obligation bridge | `deltaIterative_not_RepairObligationBridge` |
| G4-NC-9 | Delta degenerate does not imply harm bridge | `deltaDegenerate_not_HarmBridge` |
| G4-VI-1 | valid insight yields transformable insight case | `ValidInsightSem.toTransformableInsightCase` |
| G4-VI-2 | valid insight entails contradiction-addressed semantic predicate | `ValidInsightSem_addresses_contradiction` |
| G4-VI-3 | valid-insight-only witness is transformable | `validInsightOnly_transformable` |
| G4-VI-4 | valid-insight-only witness addresses contradiction | `validInsightOnly_addresses_contradiction` |
| G4-NC-10 | valid insight does not imply finality satisfaction | `validInsightOnly_not_finality` |
| G4-NC-11 | valid insight does not imply repair-closure satisfaction | `validInsightOnly_not_repairClosure` |

## Gate 5 Evaluator Calculus

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G5-VAL-1 | acceptance, rejection, abstention, and error are distinct output values | `evaluation_accepts_ne_rejects`, `evaluation_accepts_ne_abstains`, `evaluation_accepts_ne_error` |
| G5-DEC-1 | satisfied accepting decision warrants evaluator acceptance | `accepting_decision_to_accepts` |
| G5-DEC-BLOCK-1 | missing decision criteria block warranted accepting decision | `decision_missing_criteria_blocks` |
| G5-DEC-BLOCK-2 | uninspected decision evidence blocks warranted accepting decision | `decision_uninspected_evidence_blocks` |
| G5-DEC-BLOCK-3 | unapplied decision criteria block warranted accepting decision | `decision_unapplied_criteria_blocks` |
| G5-DEC-BLOCK-4 | decision scope mismatch blocks warranted accepting decision | `decision_scope_mismatch_blocks` |
| G5-DEC-BLOCK-5 | decision error blocks warranted accepting decision | `decision_error_blocks` |
| G5-ERR-1 | detected, classified, unresolved evaluator error blocks acceptance warrant | `detected_error_blocks_acceptance_warrant` |
| G5-INC-1 | missing criteria yields evaluator incompleteness | `missing_criteria_yields_incomplete_case` |
| G5-INC-2 | insufficient evidence yields evaluator incompleteness | `insufficient_evidence_yields_incomplete_case` |
| G5-INC-3 | unresolved conflict yields evaluator incompleteness | `unresolved_conflict_yields_incomplete_case` |
| G5-COMP-1 | criteria-relative completeness plus domain conclusion yields acceptance | `criteria_relative_completeness_to_acceptance` |
| G5-COMP-2 | complete criteria profile witness is satisfied | `completeCriteriaOnlyProfile_satisfied` |
| G5-COMP-BLOCK-1 | unbounded domain blocks criteria completeness | `unbounded_domain_blocks_criteria_completeness` |
| G5-COMP-BLOCK-2 | partial criteria block criteria completeness | `partial_criteria_blocks_criteria_completeness` |
| G5-COMP-BLOCK-3 | unavailable evidence blocks criteria completeness | `unavailable_evidence_blocks_criteria_completeness` |
| G5-COMP-BLOCK-4 | unresolved conflict blocks criteria completeness | `unresolved_conflict_blocks_criteria_completeness` |
| G5-COMP-BLOCK-5 | missing abstention rule blocks criteria completeness | `missing_abstention_rule_blocks_criteria_completeness` |
| G5-COMP-BLOCK-6 | missing error rule blocks criteria completeness | `missing_error_rule_blocks_criteria_completeness` |
| G5-META-1 | meta-evaluator case preserves only primary evaluator acceptance | `meta_evaluator_case_to_primary_accepts`, `metaEvaluatorOnly_primary_accepts` |
| G5-CHAIN-1 | evaluator chain case projects first evaluator acceptance | `evaluator_chain_to_first_accepts` |
| G5-CHAIN-2 | evaluator chain case projects second evaluator acceptance | `evaluator_chain_to_second_accepts` |
| G5-WIT-1 | accepting decision witness is satisfied and accepts | `acceptingDecisionOnly_satisfied`, `acceptingDecisionOnly_accepts` |
| G5-WIT-2 | rejection-only witness is satisfied | `rejectionOnly_satisfied` |
| G5-WIT-3 | abstention-only witness is satisfied | `abstentionOnly_satisfied` |
| G5-WIT-4 | error-only witness is satisfied | `errorOnly_satisfied` |
| G5-WIT-5 | incomplete-only witness is satisfied | `incompleteOnly_satisfied` |
| G5-NC-1 | evaluator-chain consensus does not imply valid insight | `chainOnly_satisfied`, `chainOnly_not_ValidInsightSem` |
| G5-NC-2 | evaluator-chain consensus does not imply full empirical validation | `chainOnly_satisfied`, `chainOnly_not_FullEmpiricalValidationSem` |
| G5-NC-3 | evaluator acceptance does not imply full empirical validation | `evaluatorOnly_acceptance_not_full_empirical_validation` |
| G5-NC-4 | meta-evaluator endorsement does not imply valid insight | `metaEvaluatorOnly_satisfied`, `metaEvaluatorOnly_not_ValidInsightSem` |
| G5-NC-5 | meta-evaluator endorsement does not imply full empirical validation | `metaEvaluatorOnly_satisfied`, `metaEvaluatorOnly_not_FullEmpiricalValidationSem` |
| G5-NC-6 | rejection-only witness does not imply valid insight | `rejectionOnly_not_ValidInsightSem` |
| G5-NC-7 | abstention-only witness does not imply valid insight | `abstentionOnly_not_ValidInsightSem` |
| G5-NC-8 | error-only witness does not imply valid insight | `errorOnly_not_ValidInsightSem` |
| G5-NC-9 | incomplete-only witness does not imply valid insight | `incompleteOnly_not_ValidInsightSem` |
| G5-NC-10 | rejection-only witness does not imply full empirical validation | `rejectionOnly_not_FullEmpiricalValidationSem` |
| G5-NC-11 | abstention-only witness does not imply full empirical validation | `abstentionOnly_not_FullEmpiricalValidationSem` |
| G5-NC-12 | error-only witness does not imply full empirical validation | `errorOnly_not_FullEmpiricalValidationSem` |
| G5-NC-13 | incomplete-only witness does not imply full empirical validation | `incompleteOnly_not_FullEmpiricalValidationSem` |
| G5-CAL-1 | high evaluator score yields accepting decision | `high_score_accepts` |
| G5-CAL-2 | medium evaluator score yields abstaining decision | `medium_score_abstains` |
| G5-CAL-3 | low evaluator score yields rejecting decision | `low_score_rejects` |
| G5-CAL-4 | low and medium scores do not yield accepting decisions | `low_score_not_accepts`, `medium_score_not_accepts` |
| G5-DIS-1 | high and low scores disagree at the decision level | `high_low_scores_disagree` |
| G5-DIS-2 | high and medium scores disagree at the decision level | `high_medium_scores_disagree` |
| G5-AGG-1 | two high scores and one low score aggregate to acceptance | `two_high_one_low_majority_accepts` |
| G5-AGG-2 | one high score and two low scores aggregate to rejection | `one_high_two_low_majority_rejects` |
| G5-AGG-3 | one high score and two medium scores aggregate to abstention | `one_high_two_medium_majority_abstains` |
| G5-AGG-4 | two high scores satisfy the at-least-two-accept predicate | `atLeastTwoAccept_two_high_one_low` |
| G5-AGG-5 | one high score and two medium scores do not satisfy at-least-two-accept | `not_atLeastTwoAccept_one_high_two_medium` |

## Gate 6 ISFT Mechanism System

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G6-LABEL-1 | M8 has mechanism index 8 | `mechanismIndex_M8` |
| G6-LABEL-2 | M12 has mechanism index 12 | `mechanismIndex_M12` |
| G6-LABEL-3 | M8 and M12 are distinct mechanism labels | `M8_ne_M12` |
| G6-SRC-1 | source mechanism names are encoded for M1-M12 | `mechanismName` |
| G6-SRC-2 | workbook marks M1-M7 and M9-M11 accepted | `workbook_M1_accepted`, `workbook_M2_accepted`, `workbook_M3_accepted`, `workbook_M4_accepted`, `workbook_M5_accepted`, `workbook_M6_accepted`, `workbook_M7_accepted`, `workbook_M9_accepted`, `workbook_M10_accepted`, `workbook_M11_accepted` |
| G6-SRC-3 | workbook marks M8 and M12 pending, not accepted | `workbook_M8_pending`, `workbook_M12_pending`, `workbook_M8_not_accepted`, `workbook_M12_not_accepted` |
| G6-PROF-1 | satisfied mechanism profile yields mechanism case data | `ISFTMechanismProfile.toCase` |
| G6-PROF-BLOCK-1 | missing mechanism domain blocks profile | `missing_mechanism_domain_blocks_profile` |
| G6-PROF-BLOCK-2 | missing mechanism trigger blocks profile | `missing_mechanism_trigger_blocks_profile` |
| G6-PROF-BLOCK-3 | missing claim basis blocks profile | `missing_mechanism_claim_basis_blocks_profile` |
| G6-PROF-BLOCK-4 | missing support basis blocks profile | `missing_mechanism_support_basis_blocks_profile` |
| G6-PROF-BLOCK-5 | missing adequacy standard blocks profile | `missing_mechanism_adequacy_blocks_profile` |
| G6-PROF-BLOCK-6 | missing evaluator boundary blocks profile | `missing_mechanism_evaluator_boundary_blocks_profile` |
| G6-PROF-BLOCK-7 | missing non-collapse boundary blocks profile | `missing_mechanism_noncollapse_boundary_blocks_profile` |
| G6-GRAPH-1 | index-increasing dependency graphs have no self-dependency | `index_increasing_graph_has_no_self_dependency` |
| G6-GRAPH-2 | linear dependency graph links M1 to M2 | `linear_graph_M1_to_M2` |
| G6-GRAPH-3 | linear dependency graph links M7 to M8 | `linear_graph_M7_to_M8` |
| G6-GRAPH-4 | linear dependency graph links M11 to M12 | `linear_graph_M11_to_M12` |
| G6-SUITE-1 | bounded ISFT suite is complete over its twelve mechanism profiles | `bounded_suite_complete`, `mechanismOnlySuite_complete` |
| G6-SUITE-2 | bounded suite covers M8 | `bounded_suite_covers_M8`, `mechanismOnlySuite_covers_M8` |
| G6-SUITE-3 | bounded suite covers M12 | `bounded_suite_covers_M12`, `mechanismOnlySuite_covers_M12` |
| G6-M8-1 | M8 power-erasure case maps to M8 mechanism profile | `M8PowerErasureCase.toMechanismProfile`, `M8PowerErasureCase_mechanism_label` |
| G6-M8-2 | M8 power-erasure case has satisfied mechanism profile | `M8PowerErasureCase_mechanism_profile_satisfied` |
| G6-M8-3 | M8 mechanism power case yields `M8Sem` | `M8_mechanism_power_case_to_M8Sem` |
| G6-M12-1 | M12 boundary profile maps to M12 mechanism profile | `M12BoundaryProfile.toMechanismProfile`, `M12BoundaryProfile_mechanism_label` |
| G6-M12-2 | satisfied M12 boundary profile yields satisfied mechanism profile | `M12BoundaryProfile_to_mechanism_satisfied` |
| G6-M12-3 | concrete M12 boundary witness is satisfied | `m12BoundaryOnlyProfile_satisfied`, `m12BoundaryOnly_to_mechanism_satisfied` |
| G6-M12-BLOCK-1 | missing M12 boundary blocks profile | `missing_M12_boundary_blocks_profile` |
| G6-M12-BLOCK-2 | missing M12 upstream enumeration blocks profile | `missing_M12_upstream_enumeration_blocks_profile` |
| G6-M12-BLOCK-3 | missing M12 scope blocks profile | `missing_M12_scope_blocks_profile` |
| G6-M12-BLOCK-4 | missing M12 non-finality blocks profile | `missing_M12_nonfinality_blocks_profile` |
| G6-M12-BLOCK-5 | missing M12 bridge separation blocks profile | `missing_M12_bridge_separation_blocks_profile` |
| G6-M12-BLOCK-6 | missing M12 empirical separation blocks profile | `missing_M12_empirical_separation_blocks_profile` |
| G6-SUPP-1 | satisfied suppression profile warrants support degradation | `SuppressionProfile_to_supportDegraded`, `suppressionOnly_supportDegraded` |
| G6-SUPP-BLOCK-1 | missing suppression support basis blocks profile | `missing_suppression_support_basis_blocks_profile` |
| G6-SUPP-BLOCK-2 | undetected suppression blocks profile | `undetected_suppression_blocks_profile` |
| G6-SUPP-BLOCK-3 | immaterial suppression blocks profile | `immaterial_suppression_blocks_profile` |
| G6-SUPP-BLOCK-4 | suppression scope mismatch blocks profile | `suppression_scope_mismatch_blocks_profile` |
| G6-NC-1 | generic mechanism profile witness does not imply ISF | `mechanismOnly_profile_not_ISFSem`, `mechanismOnly_M1_not_ISFSem` |
| G6-NC-2 | mechanism-only M8 witness does not imply `M8Sem` | `mechanismOnly_M8_not_M8Sem` |
| G6-NC-3 | M12 mechanism-only witness does not imply valid insight | `mechanismOnly_M12_not_ValidInsightSem` |
| G6-NC-4 | M12 mechanism-only witness does not imply full empirical validation | `mechanismOnly_M12_not_FullEmpiricalValidationSem` |
| G6-NC-5 | suppression-only witness does not imply ISF | `suppressionOnly_not_ISFSem` |

## Gate 7 Adequacy, Normative Bridges, And Repair

Status: MC3-Lean after successful local build.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| G7-BRIDGE-1 | conclusion-only bridge schema applies when premises, scope, and defeaters are satisfied | `conclusionOnlySchema_applies` |
| G7-BRIDGE-2 | conclusion-only bridge schema warrants its conclusion semantics | `conclusionOnlySchema_to_sem` |
| G7-BRIDGE-3 | harm bridge schema instance warrants harm conclusion | `harm_schema_to_sem` |
| G7-BRIDGE-4 | responsibility bridge schema instance warrants responsibility conclusion | `responsibility_schema_to_sem` |
| G7-BRIDGE-5 | repair-obligation bridge schema instance warrants repair-obligation conclusion | `repair_obligation_schema_to_sem` |
| G7-BRIDGE-6 | accountability bridge schema instance warrants accountability conclusion | `accountability_schema_to_sem` |
| G7-BRIDGE-7 | legal-illegitimacy bridge schema instance warrants legal-illegitimacy conclusion | `legal_illegitimacy_schema_to_sem` |
| G7-BRIDGE-8 | governance-legitimacy bridge schema instance warrants governance-legitimacy conclusion | `governance_legitimacy_schema_to_sem` |
| G7-BRIDGE-9 | moral-guilt bridge schema instance warrants moral-guilt conclusion | `moral_guilt_schema_to_sem` |
| G7-REPAIR-1 | satisfied repair diagnosis warrants repair-obligation bridge | `RepairDiagnosisProfile_to_repairObligation`, `repairBridgeOnly_has_repairObligation` |
| G7-REPAIR-BLOCK-1 | missing repair need blocks diagnosis | `missing_repair_need_blocks_diagnosis` |
| G7-REPAIR-BLOCK-2 | missing standing blocks diagnosis | `missing_repair_standing_blocks_diagnosis` |
| G7-REPAIR-BLOCK-3 | missing causal path blocks diagnosis | `missing_repair_causal_path_blocks_diagnosis` |
| G7-REPAIR-BLOCK-4 | repair scope failure blocks diagnosis | `repair_scope_failure_blocks_diagnosis` |
| G7-REPAIR-BLOCK-5 | no affected-group consultation blocks diagnosis | `no_group_consultation_blocks_diagnosis` |
| G7-REPAIR-BLOCK-6 | repair defeater blocks diagnosis | `repair_defeater_blocks_diagnosis` |
| G7-PLAN-1 | repair plan witness is satisfied | `repairBridgeOnlyPlan_satisfied` |
| G7-ACTION-1 | repair action witness is satisfied | `repairBridgeOnlyAction_satisfied` |
| G7-VERIFY-1 | repair verification witness is satisfied | `repairBridgeOnlyVerification_satisfied` |
| G7-CLOSURE-1 | repair closure witness is satisfied | `repairBridgeOnlyClosure_satisfied` |
| G7-REGRESS-1 | repair regress witness is satisfied | `repairBridgeOnlyRegress_satisfied` |
| G7-EXT-1 | repair externality witness is satisfied | `repairBridgeOnlyExternality_satisfied` |
| G7-DEFEAT-1 | defeated repair bridge schema is blocked | `defeatedRepairSchema_blocked` |
| G7-NC-1 | repair-obligation bridge does not imply harm bridge | `repairBridgeOnly_not_HarmBridgeSem` |
| G7-NC-2 | repair-obligation bridge does not imply moral-guilt bridge | `repairBridgeOnly_not_MoralGuiltBridgeSem` |
| G7-NC-3 | repair-obligation bridge does not imply full empirical validation | `repairBridgeOnly_not_FullEmpiricalValidationSem` |
| G7-NC-4 | repair-obligation bridge does not imply valid insight | `repairBridgeOnly_not_ValidInsightSem` |
| G7-NC-5 | harm bridge does not imply repair-obligation bridge | `harmBridgeOnly_has_HarmBridgeSem`, `harmBridgeOnly_not_RepairObligationBridgeSem` |
| G7-NC-6 | repair closure alone does not imply full empirical validation | `repairClosureOnly_not_FullEmpiricalValidationSem` |
| G7-NC-7 | repair closure alone does not imply moral guilt | `repairClosureOnly_not_MoralGuiltBridgeSem` |

## Gate 8 Executable Finite Checking

Status: EFC-bounded after successful local Python run.

| ID | Statement | Artifact |
| --- | --- | --- |
| G8-EFC-1 | bounded checker enumerates target-relevant Boolean valuations | `python/finite_check.py` |
| G8-EFC-2 | bounded coverage file records all 10 target results | `docs/finite_checks/coverage.json` |
| G8-EFC-3 | combined witness file records all found counterexamples | `docs/finite_checks/witnesses.json` |
| G8-EFC-4 | uses-only counterexample witness recorded | `docs/finite_checks/EFC-ISF-USES-NOT-ISF.json` |
| G8-EFC-5 | ISF-not-M8 counterexample witness recorded | `docs/finite_checks/EFC-M8-ISF-NOT-M8.json` |
| G8-EFC-6 | M8-not-harm counterexample witness recorded | `docs/finite_checks/EFC-M8-NOT-HARM.json` |
| G8-EFC-7 | evaluator-acceptance-not-valid-insight witness recorded | `docs/finite_checks/EFC-EVAL-NOT-VALID-INSIGHT.json` |
| G8-EFC-8 | valid-insight-not-empirical-truth witness recorded | `docs/finite_checks/EFC-VALID-INSIGHT-NOT-EMPIRICAL-TRUTH.json` |
| G8-EFC-9 | valid-insight-not-repair witness recorded | `docs/finite_checks/EFC-VALID-INSIGHT-NOT-REPAIR.json` |
| G8-EFC-10 | empirical-validation-not-governance-legitimacy witness recorded | `docs/finite_checks/EFC-EMPIRICAL-VALIDATION-NOT-GOVERNANCE.json` |
| G8-EFC-11 | finite check report records EFC-bounded scope and anti-overclaim guard | `docs/FINITE_CHECK_REPORT_2026-06-07.md` |
| G8-GRC-1 | bounded granularity checker enumerates three-item reflexive relations and refinement pairs | `python/granularity_check.py` |
| G8-GRC-2 | bounded granularity sweep has zero refinement-law failures | `docs/granularity_checks/summary.json` |
| G8-GRC-3 | bounded granularity sweep records converse-failure witnesses | `docs/granularity_checks/converse_failures.json` |
| G8-GRC-4 | granularity check report records GRC-bounded scope and anti-overclaim guard | `docs/GRANULARITY_CHECK_REPORT_2026-06-08.md` |
| G8-GRC-5 | granularity checker records a Lean-named payload witness and verifies it is generated | `docs/granularity_checks/lean_named_witnesses.json`, `mask_payload_converse_failure` |
| G8-DLC-1 | bounded Delta checker computes reachability, stability, finality, and resolution for the two Lean-mirrored systems | `python/delta_check.py` |
| G8-DLC-2 | bounded Delta checker records coverage for `twoDeltaSystem` and `loopDeltaSystem` | `docs/delta_checks/coverage.json` |
| G8-DLC-3 | bounded Delta checker verifies three Lean-named witnesses are supported | `docs/delta_checks/lean_named_witnesses.json` |
| G8-DLC-4 | Delta check report records DLC-bounded scope and anti-overclaim guard | `docs/DELTA_CHECK_REPORT_2026-06-08.md` |
| G8-DLC-5 | bounded Delta checker records closure candidates for the two-state Delta system | `docs/delta_checks/closure_records.json` |
| G8-DLC-6 | bounded Delta checker verifies closure-related Lean-named witnesses are supported | `docs/delta_checks/lean_named_witnesses.json`, `twoDelta_start_only_not_closed` |
| G8-DLC-7 | bounded Delta checker exhaustively sweeps all two-state systems over iterative/resolution outcomes | `docs/delta_checks/two_state_sweep.json` |
| G8-DLC-8 | bounded two-state Delta sweep records zero reachable-closure and always-implies-eventually failures | `docs/delta_checks/two_state_sweep_summary.json` |
| G8-DLC-9 | bounded Delta checker exhaustively sweeps all three-state systems over iterative/resolution outcomes | `docs/delta_checks/three_state_sweep.json` |
| G8-DLC-10 | bounded three-state Delta sweep records zero reachable-closure and always-implies-eventually failures | `docs/delta_checks/three_state_sweep_summary.json` |
| G8-RRC-1 | bounded repair-revision checker mirrors the finite ranked repair semantics | `python/repair_revision_check.py` |
| G8-RRC-2 | bounded repair-revision checker verifies Lean-named repair witnesses | `docs/repair_revision_checks/lean_named_witnesses.json` |
| G8-RRC-3 | bounded repair-revision sweep checks 256 action-result maps and 1024 action evaluations | `docs/repair_revision_checks/sweep_summary.json` |
| G8-RRC-4 | repair-revision check report records RRC-bounded scope and anti-overclaim guard | `docs/REPAIR_REVISION_CHECK_REPORT_2026-06-08.md` |
| G8-RRC-5 | bounded repair-revision checker verifies finite postulate-independence witnesses | `docs/repair_revision_checks/postulate_independence_summary.json` |
| G8-ECC-1 | bounded evaluator calibration checker mirrors finite score and majority semantics | `python/evaluator_calibration_check.py` |
| G8-ECC-2 | bounded evaluator calibration checker verifies Lean-named evaluator witnesses | `docs/evaluator_calibration_checks/lean_named_witnesses.json` |
| G8-ECC-3 | bounded evaluator calibration checker exhaustively sweeps all 27 three-score triples | `docs/evaluator_calibration_checks/summary.json` |
| G8-ECC-4 | evaluator calibration check report records ECC-bounded scope and anti-overclaim guard | `docs/EVALUATOR_CALIBRATION_CHECK_REPORT_2026-06-08.md` |
| G8-PPC-1 | bounded propositional proof checker truth-table checks Lean-named proof-theory examples | `python/propositional_proof_check.py` |
| G8-PPC-2 | bounded propositional proof checker records seven positive and negative targets | `docs/propositional_proof_checks/coverage.json` |
| G8-PPC-3 | propositional proof check report records PPC-bounded scope and anti-overclaim guard | `docs/PROPOSITIONAL_PROOF_CHECK_REPORT_2026-06-08.md` |

## Gate 9 Custom Proof Checker

Status: PYC-pass after successful local Python run.

| ID | Statement | Artifact |
| --- | --- | --- |
| G9-PYC-1 | proof checker validates premise and named-rule trace steps | `python/proof_check.py` |
| G9-PYC-2 | proof-check coverage records 8 rules and 6 traces | `docs/proof_checks/coverage.json` |
| G9-PYC-3 | ISF-to-Uses trace accepted | `docs/proof_checks/PYC-ISF-USES.json` |
| G9-PYC-4 | M8-to-ISF trace accepted | `docs/proof_checks/PYC-M8-ISF.json` |
| G9-PYC-5 | M8-to-Uses trace accepted | `docs/proof_checks/PYC-M8-USES.json` |
| G9-PYC-6 | ValidInsight-to-EvaluatorAccepts trace accepted | `docs/proof_checks/PYC-VALID-INSIGHT-EVAL.json` |
| G9-PYC-7 | EvaluatorAccepts-to-ValidInsight unsupported jump rejected | `docs/proof_checks/PYC-REJECT-EVAL-TO-VALID-INSIGHT.json` |
| G9-PYC-8 | M8 rule application with missing M8 premise rejected | `docs/proof_checks/PYC-REJECT-MISSING-M8-PREMISE.json` |
| G9-PYC-9 | proof-check report records PYC-only scope guard | `docs/PROOF_CHECK_REPORT_2026-06-07.md` |

## Gate 10 Empirical Operationalization

Status: EMP0 protocol artifacts only.

| ID | Statement | Artifact |
| --- | --- | --- |
| G10-EMP-1 | empirical coding manual drafted | `docs/empirical/CODING_MANUAL.md` |
| G10-EMP-2 | dataset schema drafted | `docs/empirical/DATASET_SCHEMA.json` |
| G10-EMP-3 | measurement protocol drafted | `docs/empirical/MEASUREMENT_PROTOCOL.md` |
| G10-EMP-4 | reliability plan drafted | `docs/empirical/RELIABILITY_PLAN.md` |
| G10-EMP-5 | construct-validity plan drafted | `docs/empirical/VALIDITY_PLAN.md` |
| G10-EMP-6 | pilot protocol drafted | `docs/empirical/PILOT_PROTOCOL.md` |
| G10-EMP-7 | replication plan drafted | `docs/empirical/REPLICATION_PLAN.md` |
| G10-EMP-8 | empirical operationalization report records EMP0 boundary | `docs/EMPIRICAL_OPERATIONALIZATION_2026-06-07.md` |

## Gate 11 Academic Rigor And Novelty Audit

Status: internal academic-rigor artifacts only.

| ID | Statement | Artifact |
| --- | --- | --- |
| G11-ACAD-1 | literature comparison matrix drafted | `docs/academic/LITERATURE_COMPARISON_MATRIX.md` |
| G11-ACAD-2 | reducibility/non-reducibility audit drafted | `docs/academic/REDUCIBILITY_AUDIT.md` |
| G11-ACAD-3 | related-work mapping drafted | `docs/academic/RELATED_WORK_MAPPING.md` |
| G11-ACAD-4 | external-review packet outline drafted | `docs/academic/EXTERNAL_REVIEW_PACKET.md` |
| G11-ACAD-5 | claims and limitations statement drafted | `docs/academic/CLAIMS_AND_LIMITATIONS.md` |
| G11-ACAD-6 | academic-rigor audit report records internal-review boundary | `docs/ACADEMIC_RIGOR_AUDIT_2026-06-07.md` |
