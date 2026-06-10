# Bottleneck 1 - Unified Type Signature And Model Semantics

Status: active formalization, MC3-Lean for encoded statements after successful
local build on 2026-06-07.

## Objective

The attached audit requires the first mathematical bottleneck to define a
unified Paralogic / ISFT type signature and model semantics before expanding
the theory. This file records the current local development state.

## Definitions Added

Lean source: `src/Paralogic/ModelSemantics.lean`.

Definitions now present:

1. `FunctionSymbol`
2. `FunctionArity`
3. `functionArity`
4. `PredicateSymbol`
5. `PredicateArity`
6. `predicateArity`
7. `Args`, a typed heterogeneous argument list indexed by sort signatures
8. `SigmaModel`, a many-sorted model with carrier family, function
   interpretation, and predicate interpretation
9. `Assignment`
10. `updateAssignment`
11. `Term`
12. `Substitution`
13. `identitySubstitution`
14. `maskSubstitution`
15. `substTerm`
16. `substArgs`
17. `TermHasVar`
18. `ArgsHaveVar`
19. `evalTerm`
20. `Formula`
21. `substFormula`
22. `FormulaHasFreeVar`
23. `SatisfiesFormula`
24. `SatisfiesAll`
25. `SemanticallyEntails`
26. `SemanticCountermodel`

Semantic predicates now present:

1. `UsesSem`
2. `ClaimsSem`
3. `SupportDegradedSem`
4. `TreatsAsAdequateSem`
5. `ISFSem`
6. `PowerRelevantSem`
7. `PowerValidityDependenceSem`
8. `PowerOmittedSem`
9. `M8Sem`
10. `CandidateInsightSem`
11. `EvaluatorAcceptsSem`
12. `LicensedTransitionSem`
13. `NonTrivialTransformationSem`
14. `ContradictionAddressedSem`
15. `NoHigherOrderDefeaterSem`
16. `GenerativityMinimalSem`
17. `DirectionalNonEquivalenceSem`
18. `ValidInsightSem`
19. `HarmBridgeSem`
20. `MoralGuiltBridgeSem`
21. `RepairObligationBridgeSem`
22. `EmpiricalValidationSem`
23. `ConstructValidSem`
24. `FullEmpiricalValidationSem`

Frame/context definitions now present:

1. `SortMap`
2. `FunctionPreservingMap`
3. `ModelHom`
4. `identityModelHom`
5. `FrameContextMorphism`
6. `identityFrameContextMorphism`
7. `PreservationProfile`
8. `totalPreservationProfile`
9. `minimalFrameProfile`

Normative bridge definitions now present:

1. `NormativeConclusion`
2. `NormativeConclusionSem`
3. `NormativeBridgeSchema`
4. `BridgeApplies`
5. `BridgeDoesNotApply`

Empirical validation definitions now present:

1. `EmpiricalValidationProtocol`
2. `EmpiricalProtocolApplies`
3. `EmpiricalProtocolBlocked`

Finite valuation definitions now present:

1. `allFunctionSymbols`
2. `allPredicateSymbols`
3. `PredicateValuation`
4. `overwriteValuation`
5. `allPredicateValuationsFrom`
6. `allPredicateValuations`
7. `finitePredicateModel`
8. `FormulaHoldsInValuation`
9. `CounterexampleValuation`
10. `SearchSpaceHasCounterexample`

Adequacy definitions now present:

1. `AdequacyDomain`
2. `AdequacyProfile`
3. `AdequacyProfileSatisfied`
4. `AdequacyProfileBlocked`

Evaluator definitions now present:

1. `EvaluationValue`
2. `EvaluatorCriteria`
3. `EvaluatorCriteriaSatisfied`
4. `EvaluatorCriteriaBlocked`
5. `CriteriaRelativeSoundness`
6. `EvaluatorRejection`
7. `EvaluatorAbstention`

M8 power definitions now present:

1. `PowerDimension`
2. `PowerConditionProfile`
3. `PowerConditionProfileSatisfied`
4. `M8PowerErasureCase`
5. `M8PowerErasureSatisfied`
6. `PowerProfileBlocked`

## Theorems Added

1. `M8Sem_to_ISFSem`
2. `ValidInsightSem_to_EvaluatorAccepts`
3. `m8Only_is_M8Sem`
4. `m8Only_not_harmBridge`
5. `m8Only_not_moralGuiltBridge`
6. `m8Only_not_repairObligationBridge`
7. `evaluatorOnly_accepts_sem`
8. `evaluatorOnly_not_ValidInsightSem`
9. `validInsightOnly_is_ValidInsightSem`
10. `validInsightOnly_not_FullEmpiricalValidationSem`
11. `empiricalNominal_has_EmpiricalValidationSem`
12. `empiricalNominal_not_FullEmpiricalValidationSem`
13. `ModelHom_preserves_UsesSem`
14. `ModelHom_preserves_ClaimsSem`
15. `ModelHom_preserves_ISFSem`
16. `ModelHom_preserves_EvaluatorAcceptsSem`
17. `ModelHom_preserves_ValidInsightSem`
18. `NormativeBridgeSchema_to_conclusion`
19. `missing_premise_blocks_bridge`
20. `scope_failure_blocks_bridge`
21. `defeater_blocks_bridge`
22. `EmpiricalValidationProtocol_to_full_validation`
23. `no_operationalization_blocks_empirical_protocol`
24. `no_construct_validity_blocks_empirical_protocol`
25. `no_reliability_blocks_empirical_protocol`
26. `no_replication_blocks_empirical_protocol`
27. `finitePredicateModel_predicate_true`
28. `finitePredicateModel_predicate_false`
29. `AdequacyProfile_to_AdequateSem`
30. `irrelevance_blocks_adequacy`
31. `insufficiency_blocks_adequacy`
32. `stale_support_blocks_adequacy`
33. `method_mismatch_blocks_adequacy`
34. `unbounded_uncertainty_blocks_adequacy`
35. `scope_mismatch_blocks_adequacy`
36. `EvaluatorCriteria_to_accepts`
37. `missing_criteria_declaration_blocks_acceptance`
38. `irrelevant_criteria_blocks_acceptance`
39. `uninspected_evidence_blocks_acceptance`
40. `unapplied_criteria_blocks_acceptance`
41. `evaluation_error_blocks_acceptance`
42. `criteria_relative_soundness_to_conclusion`
43. `rejection_noncollapse`
44. `abstention_noncollapse`
45. `PowerConditionProfile_to_powerRelevant`
46. `PowerConditionProfile_to_powerValidityDependence`
47. `PowerConditionProfile_to_powerOmitted`
48. `M8PowerErasureCase_to_M8Sem`
49. `irrelevant_power_blocks_profile`
50. `represented_power_blocks_profile`
51. `immaterial_omission_blocks_profile`
52. `immaterial_affected_group_blocks_profile`
53. `disclosed_power_blocks_profile`
54. `mitigated_power_blocks_profile`

## Countermodels Added

`m8OnlyModel` is a one-element many-sorted semantic model in which the M8
antecedent predicates hold but the normative bridge predicates do not. It
protects the boundary:

M8 does not imply harm, moral guilt, or repair obligation without an explicit
normative bridge.

`evaluatorOnlyModel` protects the boundary that evaluator acceptance does not
imply ValidInsight.

`validInsightOnlyModel` protects the boundary that ValidInsight does not imply
full empirical validation.

`empiricalNominalModel` protects the boundary that a nominal empirical
validation predicate does not imply construct validity, reliability testing, or
external replication.

## Non-Collapse Audit

Protected:

1. M8 is not harm.
2. M8 is not moral guilt.
3. M8 is not repair obligation.
4. ValidInsight is not evaluator-independent truth.
5. Empirical validation remains separate from construct validity,
   reliability, and external replication.
6. A carrier map does not preserve meaning unless preservation obligations are
   part of the morphism.
7. A normative conclusion requires a bridge schema with premises, scope,
   defeater absence, and a warrant.
8. Full empirical validation requires a protocol with operationalization,
   construct boundaries, construct validity, reliability testing, external
   replication, domain scope, limitations, and a warrant.
9. Finite counterexample claims must be grounded in a valuation and formula
   pair; the mere existence of the framework is not itself a completed search.
10. Adequacy is domain-relative and condition-gated; it is not a bare label.
11. Evaluator acceptance is criteria-relative and error-gated; it is not truth.
12. M8 power erasure requires relevance, omission, materiality, affected-group
   materiality, absent disclosure, absent mitigation, and warrants.

Still open:

1. Contradiction does not imply insight in the many-sorted layer.
2. Evaluator acceptance does not imply empirical truth in the many-sorted
   layer.
3. ValidInsight does not imply repair in the many-sorted layer.
4. Empirical validation does not imply governance legitimacy in the
   many-sorted layer.
5. ISF does not imply moral, legal, or political wrongdoing.

## Reward-Hacking Audit

Blocked in this step:

1. No claim that many-sorted syntax completes Paralogic.
2. No claim that a named one-element model is exhaustive finite search.
3. No claim that a model homomorphism exists merely because a translation is
   rhetorically plausible.
4. No claim that preserving selected predicates preserves all mathematical,
   empirical, or normative meaning.
5. No claim that empirical validation is full validation without construct
   validity, reliability testing, and external replication.
6. No claim that ISF or M8 produces harm, responsibility, repair obligation,
   accountability, legal illegitimacy, governance legitimacy, or moral guilt
   without an explicit bridge.
7. No claim that metrics, benchmarks, anecdotes, or nominal validation are full
   empirical validation.
8. No claim that finite model search has been completed merely because a search
   space has been defined.
9. No claim that evidence is adequate without relevance, sufficiency, currency,
   methodological fit, bounded uncertainty, scope match, and a warrant.
10. No claim that evaluator acceptance implies truth outside a criteria-relative
    soundness schema.
11. No claim that M8 proves harm, discrimination, illegality, moral guilt, or
    repair obligation without a normative bridge.

Current vulnerability:

The Lean source has now been locally build-checked, but this checks only the
encoded formal statements. It does not check external interpretations,
empirical protocols, normative warrant truth, or exhaustive finite-search
coverage.

## Hallucination Audit

Grounded claims:

1. The files contain explicit Lean source for many-sorted semantics.
2. The files contain explicit Lean source for quantifiers, substitution,
   free-variable checks, model homomorphisms, and preservation profiles.
3. The files contain explicit normative bridge schemas separating diagnostic
   predicates from normative conclusions.
4. The files contain explicit empirical validation protocol schemas separating
   nominal validation from full validation.
5. The files contain explicit finite valuation model definitions.
6. The files contain explicit domain-relative adequacy profile definitions.
7. The files contain explicit evaluator criteria and criteria-relative
   soundness definitions.
8. The files contain explicit M8 power-erasure condition schemas.
9. The files contain explicit named witness models for selected non-collapse
   boundaries.

Non-grounded or not-yet-earned claims:

1. The one-element witnesses are not exhaustive model enumeration.
2. The morphism layer does not yet prove category laws.
3. The formula layer does not yet prove substitution/satisfaction lemmas.
4. No concrete normative bridge has been externally justified.
5. No empirical protocol has been populated with a real dataset, coding manual,
   reliability result, or replication result.
6. The finite valuation framework has not yet produced stored witness output.
7. No concrete adequacy profile has been populated for a real domain case.
8. No concrete evaluator criteria set has been externally justified.
9. No concrete M8 power-erasure case has been externally validated.
10. No novelty, publication, empirical, legal, moral, or sociological claim is
   established by this step.

## Gap Ledger

Open mathematical gaps:

1. Substitution lemmas are not yet proven.
2. Projection, translation, and preservation profiles are not yet developed
   beyond first morphism structures.
3. Contradiction kinds are tagged, but their model semantics are still thin.
4. Evaluator soundness relative to explicit criteria is not yet defined.
5. `Adeq` remains a predicate symbol, not a domain-indexed adequacy calculus.
6. M8 still needs a full power-erasure semantics.
7. Normative bridge schemas exist, but no domain-specific bridge has been
   justified.
8. Empirical validation protocols exist, but no concrete protocol has been
   executed.
9. The finite valuation framework is present, but exhaustive run artifacts are
   not yet produced.
10. Adequacy profiles exist, but no domain-specific adequacy standard has been
   externally validated.
11. Evaluator criteria exist, but no meta-evaluator or evaluator-chain calculus
   has been developed.
12. M8 power-erasure cases exist, but no concrete domain case or finite search
   coverage result has been produced.
13. Quantifiers are present, but no proof theory for quantified formulas has
   been developed.

## Verification Status

Machine status: MC3-Lean for the encoded statements included in the successful
local `lake build` recorded in `docs/BUILD_VERIFICATION_2026-06-07.md`.

Empirical status: EMP0.

External review status: none.

## Next Dependency

The next mathematical step is to prove substitution/satisfaction lemmas, then
develop projection and translation laws for frame/context morphisms.
