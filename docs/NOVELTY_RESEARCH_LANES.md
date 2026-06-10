# Novelty Research Lanes

Status: active research program, not completion claim.

The goal is to make Paralogic novel by developing mathematical structure that
is testable, falsifiable, and connected to existing advanced mathematics,
rather than by relabeling ordinary claims.

## Lane K1 - Contextual Obstruction Semantics

External anchor: Abramsky and Brandenburger's sheaf-theoretic contextuality
program identifies contextuality with obstruction to a global section:
`https://arxiv.org/abs/1102.0264`.

Paralogic direction: frame-relative institutional readings may be locally
available but fail to glue into a single global reading.  This gives a precise
mathematical home for non-collapse, frame conflict, and irreducible local
perspective conflict.

Artifacts now added:

- `src/Paralogic/ContextualObstruction.lean`
- `CoveredPresheaf`
- `LocalFamily`
- `HasGlobalExtension`
- `ContextualObstruction`
- `CoverJointlyMonic`
- positive test: `boolPairFamily_has_global_extension`
- obstruction test: `noGlobalFamily_obstructed`

Status: MC3-Lean exploratory core.  Not yet specialized to ISFT claims,
evidence, evaluators, or repair.

## Lane K2 - Institution-Theoretic Signature Change

External anchor: institution theory was introduced as abstract model theory for
specification, and later institutional approaches organize logical theories and
local logics using categorical structure:
`https://arxiv.org/abs/1810.08074`.

Paralogic direction: treat frames, evaluators, and institutional contexts as
local logics connected by signature morphisms.  Non-preservation then becomes
a theorem about failed or non-conservative translations, not merely a prose
warning.

Current local basis:

- many-sorted signature and satisfaction in `ModelSemantics.lean`
- model homomorphism and non-preservation artifacts
- kernel embedding artifacts

Artifacts now added:

- `src/Paralogic/InstitutionFragment.lean`
- `LogicFragment`
- `FragmentTranslation`
- `SatisfactionCondition`
- positive identity test: `identityFragmentTranslation_satisfies_condition`
- non-preservation counterexample:
  `unitSyntaxTranslation_not_satisfaction_preserving`

Status: MC3-Lean exploratory core.  This is not full institution theory, but
it gives Paralogic a checked satisfaction-condition interface for local logic
translations.

Next real test:

- specialize `LogicFragment` to pointed many-sorted Paralogic models;
- add a counterexample where a frame translation preserves syntax but not a
  bridge predicate.

## Lane K3 - Coalgebraic Delta Dynamics

External anchor: coalgebraic modal logic abstracts Kripke-style transition
systems and unifies relational, probabilistic, graded, and conditional modal
semantics:
`https://users.cecs.anu.edu.au/~dpattinson/Publications/tcs2011.pdf`.

Paralogic direction: model Delta dynamics as coalgebraic transition structure
over frames, evaluator states, contradiction residue, and repair state.  This
would let Paralogic distinguish one-step transition, iterative repair,
collapse, and non-finality with modal or fixed-point operators.

Current local basis:

- `InsightDelta.lean`
- `FrameContext.lean`
- transition/blocker artifacts

Artifacts now added:

- `src/Paralogic/DeltaDynamics.lean`
- `DeltaTransitionSystem`
- `DeltaReachable`
- `DeltaClosed`
- `DeltaStable`
- `EventuallyResolution`
- `DeltaGlobalFinality`
- `EventuallyStable`
- `EventuallyStableResolution`
- `DeltaAlways`
- `DeltaEventually`
- `IsResolutionState`
- `IsStableState`
- positive finite test: `twoDelta_eventually_resolution`
- liveness counterexample: `loopDelta_not_eventually_resolution`
- invalid finality counterexample:
  `eventual_resolution_not_global_finality`
- terminal-stability counterexamples:
  `stable_resolution_not_global_finality`,
  `eventual_stability_not_eventual_resolution`
- executable Delta transition check:
  `python/delta_check.py`
- executable Delta closure records:
  `docs/delta_checks/closure_records.json`
- exhaustive two-state Delta sweep:
  `docs/delta_checks/two_state_sweep_summary.json`
- exhaustive three-state Delta sweep:
  `docs/delta_checks/three_state_sweep_summary.json`
- generated Lean-named Delta witness cross-check:
  `docs/delta_checks/lean_named_witnesses.json`
- modal reachability separations:
  `eventual_not_always_resolution_modal`,
  `eventual_stability_not_eventual_resolution_modal`
- fixed-point closure layer:
  `delta_reachable_closed`, `delta_reachable_least_closed`,
  `twoDelta_start_only_not_closed`

Status: MC3-Lean exploratory core.  It is not yet a full coalgebraic modal
logic, but it converts Delta dynamics from taxonomy toward checked transition
semantics.

Next real test:

- add sampled four-state Delta sweeps or parameterized bounded-sweep summaries;
- connect executable sweep summaries to additional Lean finite witnesses when
  useful.

## Lane K4 - Belief Revision And Minimal Repair

External anchor: AGM-style belief revision has model-theoretic
characterizations based on minimal change and preference relations:
`https://arxiv.org/abs/2112.13557`.

Paralogic direction: represent repair and frame update as constrained revision
operators.  This gives a way to test whether a proposed repair is minimal,
overreaching, undercorrecting, or non-conservative.

Current local basis:

- `Repair.lean`
- `NormativeBridge.lean`
- `Evaluator.lean`

Artifacts now added:

- `src/Paralogic/MinimalRepair.lean`
- `RepairRevisionFrame`
- `StrictlyPreferred`
- `MinimalAcceptableRepair`
- `HasMinimalRepair`
- `HasUniqueMinimalRepair`
- abstract unique-minimal theorem: `best_acceptable_unique_minimal`
- positive finite test: `twoRepair_has_minimal`
- non-uniqueness counterexample: `twoRepair_not_unique_minimal`
- ranked finite repair frame: `rankedRepairFrame`
- unique ranked minimal state: `rankedRepair_has_unique_minimal`
- ranked-frame instance of the abstract theorem:
  `rankedRepair_unique_minimal_from_best`
- revision-postulate witness: `targetedRepair_satisfies_revision_postulates`
- under-repair negative controls: `partialRepair_not_successful`,
  `doNothingRepair_not_successful`
- over-repair negative controls: `excessiveRepair_successful_not_minimal`,
  `excessiveRepair_not_revision_postulates`
- diagnosis bridge connection:
  `repairBridgeOnlyTargetedRevision_warrants_obligation`
- postulate-independence frame: `repairPostulateFrame`
- postulate-independence witnesses:
  `redundantAction_success_conservative_not_minimal`,
  `overreachAction_success_minimal_not_conservative`,
  `failedAction_conservative_not_successful`
- bounded executable repair-revision sweep:
  `python/repair_revision_check.py`
- repair-revision report:
  `docs/REPAIR_REVISION_CHECK_REPORT_2026-06-08.md`

Status: MC3-Lean plus RRC-bounded executable checking.  The lane now has both
a non-unique preferential repair frame and a ranked finite repair frame where
the adequate state is the unique minimal acceptable repair.  The executable
sweep checks all 256 action-result maps over four repair actions and four
repair states, yielding 1024 action evaluations and zero postulate-equivalence
failures.  A second finite independence table separates success, minimality,
and conservatism.

Next real test:

- generalize from the current best-state theorem to richer revision operators
  over parameterized preference relations;
- connect repair revision to richer `RepairPlanProfile`,
  `RepairVerificationProfile`, regress, and externality data.

## Lane K5 - Argumentation And Evaluator Defense

External anchor: Dung-style abstract argumentation frameworks model arguments
with an attack relation; admissibility requires more than membership in a
selected set.  See the original 1995 Artificial Intelligence paper:
`https://www.sciencedirect.com/science/article/pii/000437029400041X`.

Paralogic direction: evaluator acceptance should be separated from defended
acceptance.  A claim or argument may be selected, conflict-free, or even
procedurally accepted while still failing defense against relevant attacks.

Artifacts now added:

- `src/Paralogic/Argumentation.lean`
- `src/Paralogic/EvaluatorArgumentation.lean`
- `ArgumentationFramework`
- `ConflictFree`
- `Defends`
- `Admissible`
- `EvaluatorArgumentSelection`
- `DefendedEvaluatorAcceptance`
- positive finite test: `targetOnly_conflict_free`
- defense/admissibility counterexample: `targetOnly_not_admissible`
- evaluator-acceptance counterexample:
  `evaluator_acceptance_not_necessarily_defended`
- empty-set admissibility baseline: `emptySelection_admissible`

Status: MC3-Lean exploratory core.  It is now connected to evaluator
acceptance by a small selection record and a counterexample showing evaluator
acceptance need not be defended acceptance.

Next real test:

- define defended evaluator acceptance as a stricter schema.
- connect defended evaluator acceptance to concrete evaluator criteria.

## Lane K6 - Rough Evidence And Adequacy Approximation

External anchor: rough-set theory separates lower and upper approximation of a
target concept under an indiscernibility relation; formal concept analysis
separates objects, attributes, incidence, extents, and intents through a
Galois connection.

Paralogic direction: adequacy should distinguish definite support from
possible support and boundary ambiguity.  This is useful when evidence is
coarse, lossy, institutionally filtered, or category-mediated.  Category and
evidence formation should also distinguish shared attributes from attributes
held only by some objects.

Artifacts now added:

- `src/Paralogic/RoughEvidence.lean`
- `src/Paralogic/RoughAdequacyBridge.lean`
- `src/Paralogic/EvidenceGranularity.lean`
- `src/Paralogic/FormalConcept.lean`
- `src/Paralogic/ConceptualEssentialization.lean`
- `RoughEvidenceSpace`
- `LowerApprox`
- `UpperApprox`
- `BoundaryRegion`
- `RoughAdequacyEligible`
- `RoughAdequacyLink`
- `FormalContext`
- `ExtentToIntent`
- `IntentToExtent`
- `FormalConcept`
- `ConceptAttributionProfile`
- `ConceptAttributionSatisfied`
- `ConceptAttributionBlocked`
- positive theorem: `lower_implies_upper`
- Galois connection theorem: `formal_context_galois`
- boundary counterexamples: `twoEvidence_favorable_boundary`,
  `twoEvidence_unfavorable_boundary`
- adequacy blocker: `boundary_blocks_rough_adequacy`
- anti-overclaim theorem: `upper_not_necessarily_rough_adequacy`
- rough-to-profile bridge:
  `rough_boundary_blocks_profile_satisfaction`
- concrete blocked profile: `roughBoundaryAdequacyProfile_not_satisfied`
- granularity-refinement theorem:
  `lower_preserved_under_relation_refinement`
- finite granularity contrast:
  `granularity_changes_favorable_adequacy`
- converse-failure counterexample:
  `fine_lower_does_not_imply_coarse_lower`
- three-item Lean/checker-aligned witnesses:
  `threeEvidence_favorable_converse_failure`,
  `threeEvidence_corroborating_converse_failure`
- three-item relation-mask encoding:
  `ThreeGranularityMask`, `allThreeGranularityMasks_length`,
  `mask_payload_converse_failure`
- fine-granularity positive profile:
  `fineAdequacyProfile_satisfied`
- executable granularity sweep:
  `python/granularity_check.py`
- generated Lean-named witness cross-check:
  `docs/granularity_checks/lean_named_witnesses.json`
- evidence concept example: `documentedEvidenceConcept`
- concept-intent M7 blocker:
  `contestedDocumentedConceptProfile_blocked`
- concept-intent positive M7 witness:
  `documentedDocumentedConceptProfile_satisfied`

Status: MC3-Lean exploratory core.  It does not validate any real evidence
source; it gives checked approximation, granularity, and concept-formation
vocabulary for future adequacy work.  Formal concept intents are now connected
to a narrow M7 category-essentialization blocker, without claiming complete M7
semantics.

Next real test:

- expand Lean-named witness cross-checks beyond the identity/all-true mask
  example;
- connect the M7 concept-attribution profile to source-backed M7 mechanism
  semantics once the source resources provide enough detail.

## Anti-Reward-Hacking Rule

Each lane must produce at least one of the following before it upgrades from
research direction to local mathematical result:

- a Lean definition plus theorem;
- a finite executable checker target;
- a countermodel artifact;
- a regression test;
- an empirical protocol artifact, if the claim is empirical.

Names of advanced mathematical fields do not count as evidence.
