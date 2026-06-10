# Theorem Classification

Status: active.

The theorem ledger is too flat.  This classification prevents projection
lemmas and witness constructors from being mistaken for deep results.

| Class | Meaning | Examples | Completion Treatment |
| --- | --- | --- | --- |
| projection | extracts a field from a structure | `ISF_to_Uses`, `ValidInsightSem_to_EvaluatorAccepts` | useful, low depth |
| constructor/blocker | builds a blocker or satisfaction record | `missing_*_blocks_*` | useful, low-to-medium depth |
| structural | proves behavior of syntax/model operations | substitution lemmas, satisfaction invariance | medium-to-high depth |
| countermodel | exhibits a model separating claims | `*_not_*` witnesses | important, depth depends on model richness |
| warrant-consuming | uses a supplied warrant field | bridge/profile-to-conclusion theorems | conditional only |
| executable | Python finite/proof check artifact | EFC/PYC outputs | separate from Lean |
| empirical-protocol | protocol document without data | EMP0 artifacts | not validation |
| external-review | review packet or response | EXT artifacts | not review until received |

## Immediate Reclassification Finding

Most current theorem-ledger entries are projection, constructor/blocker,
countermodel, warrant-consuming, executable, or protocol artifacts.  The
repository has fewer substantive structural theorems than the raw theorem
count suggests.

## Repair Revision Classification

The ranked repair-revision artifacts split into three classes:

- `best_acceptable_unique_minimal` is a structural theorem about arbitrary
  repair-revision frames with an antisymmetric preference relation and a best
  acceptable state.
- `rankedRepair_has_unique_minimal` and
  `targetedRepair_satisfies_revision_postulates` are finite structural facts
  about the local ranked frame.
- `partialRepair_not_successful` and
  `excessiveRepair_not_revision_postulates` are finite negative controls.
- `redundantAction_success_conservative_not_minimal`,
  `overreachAction_success_minimal_not_conservative`, and
  `failedAction_conservative_not_successful` are finite postulate-independence
  witnesses.
- `repairBridgeOnlyTargetedRevision_warrants_obligation` remains
  warrant-consuming because the repair-obligation conclusion depends on
  `RepairDiagnosisProfile.warrantRepairObligation`.

The executable `RRC` artifacts are bounded finite checks.  They strengthen the
audit trail for this fragment, but they are not general belief-revision
representation theorems.

## Proof-Theory Classification

`derives_sound` is a structural soundness theorem for the encoded derivability
calculus.  The new implication-introduction, falsity-elimination, and
disjunction-elimination examples are soundness witnesses inside that calculus.
`derives_forall_current_example_sound` and
`derives_exists_current_example_sound` are scoped quantified derivability
witnesses for the current-value reading of quantified variables.  They are not
full natural-deduction quantifier rules with freshness/eigenvariable
conditions and they do not establish completeness.
`derives_forall_truth_example_sound` and the `PremisesStableUnderUpdate`
lemmas add a sound universal-introduction pattern under semantic
premise-stability.  This is stronger than the previous current-value-only
fragment, but it is still not a syntactic freshness/eigenvariable calculus.
`semantically_entails_forall_intro_of_stable` and its freshness variants are
structural semantic-consequence theorems matching that side condition directly,
without routing through derivability.
`satisfaction_stable_update_of_not_free` and
`derives_forall_intro_of_fresh_sound` bridge syntactic no-free-variable facts
to universal-introduction stability, including quantified formulas where
binder shadowing makes the updated variable not free.  This is a genuine
freshness result, but it is still not a full alpha-equivalence or
eigenvariable-completeness theory.
`universal_intro_without_freshness_countermodel` and
`universal_intro_without_freshness_not_semantically_valid` are countermodel
artifacts for the proof theory itself: they show that the calculus would be
unsound if universal introduction were allowed from premises containing the
generalized variable free.
The `PPC` artifacts are bounded propositional truth-table checks; they support
the examples and negative controls, but they are not a completeness theorem for
the many-sorted language.

## Model-Hom Preservation Classification

`ModelHom_preserves_evalTerm`, `ModelHom_preserves_evalArgs`, and
`ModelHom_preserves_positive_quantifier_free_satisfaction` are structural
model-theory results for the current many-sorted semantics.  Their scope is
one-way preservation for positive quantifier-free formulas only.  They do not
establish preservation for negation, implication, universal quantification, or
arbitrary formula translations.

`model_hom_not_preserve_negation_counterexample`,
`model_hom_not_preserve_implication_counterexample`, and
`model_hom_not_preserve_universal_counterexample` are countermodel artifacts.
They show that the positive-fragment restriction is mathematically active:
ordinary model homomorphisms can preserve atomic predicates forward while
failing to preserve formulas with negation, implication, or universal
quantification.

`ModelIso_reflectsPredicate` and
`ModelIso_full_formula_satisfaction_iff` are structural isomorphism results.
They upgrade one-way homomorphism preservation to reflection/equivalence under
an explicit forward/backward homomorphism inverse.  The full theorem covers
negation, implication, and quantifiers by using assignment-update transport.
It is not translation equivalence, model categoricity, or a global
completeness result.

`FormulaTranslation_preserves_satisfies_all`,
`FormulaTranslation_transports_semantic_entailment_instance`,
`identityFormulaTranslation_apply`, and `composeFormulaTranslation_apply` are
structural translation-infrastructure results.  They provide one-way premise
satisfaction preservation, identity, composition, and transport of a source
entailment instance through a satisfaction-preserving translation.  They do
not establish translation reflection, translation equivalence, or unrestricted
target-side semantic entailment for arbitrary target assignments.

## Evaluator Calibration Classification

`EvaluatorCalibration.lean` contributes finite structural facts about a local
three-level score procedure, disagreement predicates, and majority aggregation.
The `ECC` checker exhaustively tests the 27 triples available in that finite
fragment.  These artifacts are operational sanity checks, not empirical
calibration, reliability measurement, or validation of a real scoring rubric.
