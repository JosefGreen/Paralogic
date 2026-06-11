# Current Status

Last updated: 2026-06-11.

Current status: incomplete.

The repository currently contains:

- Lean-checked scaffold modules and selected theorem families.
- Selected non-collapse countermodels, many of them one-element witnesses.
- Representative two-element many-sorted finite non-collapse witnesses.
- Model-homomorphism structure with pointwise composition laws and positive
  quantifier-free formula preservation.
- Model-homomorphism non-preservation counterexamples showing that negation,
  implication, and universal quantification cannot be added to the
  preservation theorem without stronger hypotheses.
- Model-isomorphism structure with identity, composition, predicate
  reflection, assignment-update transport, and full formula satisfaction
  equivalence.
- Formula-translation identity/composition infrastructure and one-way premise
  satisfaction preservation, plus transported semantic-entailment instances
  under satisfaction-preserving translations.
- Bounded finite-check artifacts for 10 targets.
- A bounded three-item granularity checker with persisted coverage and
  converse-failure witnesses.
- A bounded Delta checker with persisted coverage and Lean-named witness
  cross-checks for the finite transition and closure examples.
- An exhaustive two-state Delta executable sweep over iterative/resolution
  outcomes and all directed step relations.
- An exhaustive three-state Delta executable sweep over iterative/resolution
  outcomes and all directed step relations.
- A bounded repair-revision checker sweeping all 256 four-action, four-state
  action-result maps and verifying 1024 action evaluations against the Lean
  repair witnesses.
- A bounded evaluator-calibration checker sweeping all 27 three-evaluator
  score triples for finite score, disagreement, and majority-decision rules.
- A bounded propositional proof checker covering seven positive and negative
  truth-table targets for the strengthened derivability fragment.
- A tiny PYC proof checker for a Horn-like fragment, with regression tests and
  persisted-artifact checks.
- A whole-system completion pipeline that keeps local formal work separate
  from empirical and external-review blockers.
- A new MC3-Lean exploratory contextual-obstruction layer for novelty work.
- A new MC3-Lean finite Delta-dynamics layer with reachability and a checked
  non-resolution loop counterexample.
- A strengthened MC3-Lean proof-theory layer with soundness for implication
  introduction, falsity elimination, disjunction elimination, and scoped
  current-value quantifier derivation examples.
- Scoped MC3-Lean quantified semantic entailment laws and derivability rules
  for universal current-value elimination, existential current-value
  introduction, and universal introduction under semantic premise-stability.
- Direct MC3-Lean semantic universal-introduction theorems under premise
  stability and under syntactic no-free-variable freshness.
- MC3-Lean free-variable agreement lemmas showing that formula satisfaction
  depends only on free variables, plus assignment-invariance for closed
  formulas and closed premise lists.
- MC3-Lean syntactic freshness lemmas that turn no-free-variable premise facts
  into assignment-update stability for universal introduction, with the older
  quantifier-free bridge retained as a bounded subcase.
- An MC3-Lean countermodel showing that unrestricted universal introduction
  from a premise with the quantified variable free is not semantically valid.
- A GitHub Actions workflow updated to use the supported Lean action, opt into
  Node 24 JavaScript actions, and run the Python regression/checker suite plus
  an active Lean-hole scan.
- A new MC3-Lean Delta finality separation showing eventual resolution does
  not imply every reachable state is resolved.
- A new MC3-Lean Delta terminal-stability separation showing stable behavior
  does not imply resolution, and stable resolution does not imply global
  finality.
- A new MC3-Lean modal Delta layer separating reachable-state always and
  eventually predicates.
- A new MC3-Lean Delta fixed-point closure layer showing reachability is the
  least transition-closed predicate containing the initial state.
- A new MC3-Lean minimal-repair layer showing minimal repair need not be
  unique, plus a ranked repair-revision layer separating targeted repair,
  under-repair, over-repair, and finite postulate-independence cases.
- A new MC3-Lean abstract-argumentation and evaluator-defense layer separating
  conflict-free selection, evaluator acceptance, and defended admissibility.
- A new MC3-Lean evaluator-calibration layer with finite score levels,
  threshold decisions, disagreement witnesses, and majority aggregation.
- A new MC3-Lean rough-evidence layer separating definite support, possible
  support, boundary ambiguity, and adequacy-profile sufficiency.
- A new MC3-Lean evidence-granularity layer proving lower approximation is
  preserved by relation refinement and showing the converse fails in a finite
  case.
- A new MC3-Lean formal-concept layer with an extent/intent Galois connection
  and a small evidence concept example.
- A new MC3-Lean concept-attribution layer connecting formal concept intents
  to a narrow M7 category-essentialization blocker.
- A new MC3-Lean institution-style local-logic fragment with satisfaction
  condition and a non-preservation counterexample.
- A new candidate-synthesized mechanism semantics tier for M1-M12, pairing
  each mechanism with an academic lens, failure axis, maturity status,
  operational trigger, boundary guard, empirical coding plan, and non-collapse
  guard before any source-backed or empirical promotion is allowed.
- A new MC3-Lean warrant-discharge scaffold that enumerates current
  warrant-like assumptions, proves they are not yet source-backed or
  empirically validated, and gives all-false-model countermodels against raw
  condition-to-conclusion shortcuts.
- A scoped operational adequacy model where adequacy is computed from
  supported evidence, in-scope context, and matched claim, including a negative
  control for unsupported evidence.
- A scoped operational evaluator model where satisfied evaluator criteria and
  high-score accepting decisions compute evaluator acceptance for an approved
  evaluator/candidate pair, while rejected candidates and low-score acceptance
  remain blocked.
- A scoped operational contradiction model where contradiction presence is
  computed from active frame, active context, and contested claim, with
  negative controls for resolved claim, inactive frame, and inactive context.
- A scoped operational M8 power-condition model where relevance, validity
  dependence, and omission are computed for a review institution, affected
  group, contested output, and material power condition, with negative controls
  for unaffected group, immaterial condition, and ordinary output.
- A scoped operational suppression model where supported evidence, matched
  context, and suppressed claim compute support degradation, with negative
  controls for unsupported evidence, mismatched context, and ordinary claim.
- A scoped operational repair-obligation model where repair-need bridge,
  responsible institution, and affected group compute repair obligation, with
  negative controls for ordinary bridge, other institution, and other group.
- A protocol-level operational empirical-validation model where full
  validation requires empirical validation, construct validity, reliability
  testing, and external replication predicates, with negative controls for
  nominal validation, unvalidated objects, and other claims.
- A conclusion-indexed operational normative-bridge model where each normative
  conclusion has a distinct bridge token, with negative controls for ordinary
  bridge, other institution, and group-sensitive harm/repair cases.
- A universal MC3-Lean warrant-coverage theorem proving every currently
  enumerated warrant obligation is operationally discharged in the scoped core,
  plus generic guards separating that status from source-backed or empirical
  promotion.
- EMP0 empirical protocol artifacts.
- Internal academic-audit artifacts.

The repository does not yet contain:

- a complete Paralogic or ISFT mathematical theory;
- source-backed semantics for all M1-M12 mechanisms;
- completed discharge of all warrant obligations into operational,
  source-backed, empirically validated, or lower-level derived theorems;
- a mature proof theory with full syntactic freshness/eigenvariable rules for
  quantified formulas, alpha-equivalence, and completeness results;
- global finite-model search;
- empirical data, reliability statistics, construct validation, or replication;
- external peer review.

Canonical audit: `docs/FULL_SYSTEM_AUDIT_2026-06-08.md`.

Canonical pipeline: `docs/ENTIRE_SYSTEM_COMPLETION_PIPELINE.md`.

Candidate mechanism synthesis:
`docs/CANDIDATE_MECHANISM_SYNTHESIS_2026-06-11.md`.

Novelty lanes: `docs/NOVELTY_RESEARCH_LANES.md`.

Older audit and pipeline documents should be read as historical snapshots
unless they agree with this status page.
