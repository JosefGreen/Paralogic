# Entire-System Completion Pipeline

Status: active.

Purpose: complete Paralogic / ISFT as an academically rigorous system without
collapsing local artifacts into global completion.

## Status Labels

| Label | Meaning |
| --- | --- |
| TODO | no artifact yet |
| SCAF | scaffold exists |
| MC3 | Lean-checked encoded statement |
| EFC | executable finite check |
| PYC | custom proof-check artifact |
| EMP0 | empirical protocol only |
| EMP1 | pilot data collected |
| EMP2 | reliability measured |
| EMP3 | construct validity assessed |
| EMP4 | independent replication completed |
| EXT0 | no external review |
| EXT1 | external review requested |
| EXT2 | external review received |
| EXT3 | revisions completed |
| PUB | publication-ready claim packet |

No item is complete unless its required status labels are met.

## Lane A - Status And Anti-Reward-Hacking Infrastructure

Exit condition: the repository has one canonical status source, stale documents
are marked as historical, theorem artifacts are classified by depth, and all
warrants are audited.

1. Canonical status page: MC3 documentation.
2. Full-system audit: MC3 documentation.
3. Warrant audit: classify every warrant field.
4. Theorem-depth ledger: projection, structural, countermodel, executable,
   empirical, external-review.
5. CI-style checks: Lean build, Python checkers, pytest, overclaim scan.

Current status: MC3/PYC/EFC scaffold complete for local status infrastructure;
GitHub Actions workflow wiring now uses the supported Lean action and runs the
Python checker suite plus an active Lean-hole scan.  Still open for
stale-document pruning and continuous enforcement across all future artifacts.

## Lane B - Formal Core And Proof Theory

Exit condition: a derivability calculus exists and has a Lean soundness theorem
against `SatisfiesFormula`; completeness is either proved for a declared
fragment or explicitly marked open.

1. Formula alpha-equivalence.
2. Capture-avoiding substitution for quantified formulas.
3. Derivability rules.
4. Soundness theorem.
5. Declared fragment completeness theorem or impossibility/open-status proof.
6. Semantic consequence countermodel suite.

Current status: MC3-Lean plus PPC-bounded executable checking for a scoped
propositional fragment.  The derivability calculus now has soundness for
premise use, truth introduction, falsity elimination, conjunction rules,
disjunction introduction/elimination, and implication introduction/elimination.
Scoped derivability rules and semantic entailment laws now cover universal
current-value elimination, existential current-value introduction, and
universal introduction under semantic premise-stability.  Syntactic
no-free-variable freshness now implies assignment-update stability for
premises, including binder-shadowing cases; the earlier quantifier-free bridge
remains as a bounded subcase.  The semantic consequence layer also has direct
universal-introduction theorems under stability and no-free-variable freshness,
matching the derivability rule's side condition.  A formal semantic
countermodel now blocks the
unsound shortcut from a premise with a free variable to its universal closure,
so the universal-introduction side condition is an active mathematical
restriction rather than documentation language.
`python/propositional_proof_check.py` truth-table checks seven positive and
negative targets.  Alpha-equivalence, syntactic freshness/eigenvariable
machinery for quantified formulas, full quantified rules, and completeness
remain open.

## Lane C - Model Theory

Exit condition: models, homomorphisms, translations, projections, and
countermodel families are nontrivial and checked beyond one-element witnesses.

1. Signature enumeration tied to signature counts.
2. Model isomorphisms.
3. Model-hom identity and associativity at structure level.
4. Formula-translation preservation theorems.
5. Projection-law theorems.
6. Two-or-more-element finite model families.
7. Parameterized countermodel families.

Current status: SCAF/MC3 partial.  Function and predicate enumerations are
count-checked, coverage-checked, and duplicate-checked.  Representative
two-element many-sorted finite model witnesses now exist for ISF/M8 boundary
countermodels.  Model homomorphisms now have pointwise identity/composition
laws, term and argument evaluation preservation, and positive quantifier-free
formula satisfaction preservation.  Formal non-preservation counterexamples
now show that ordinary model homomorphisms do not preserve negation,
implication, or universal quantification without stronger hypotheses.  Model
isomorphisms now have identity, composition, predicate reflection, and
full formula satisfaction equivalence, including quantified formulas via
assignment-update transport.  Formula translations now have identity,
composition, one-way premise-list satisfaction preservation, and transported
semantic-entailment instances for source assignments.  Structure-level
category laws, unrestricted target-side semantic-entailment preservation for
translations, and global finite-search coverage remain open.

## Lane D - ISFT M1-M12 Mechanism Semantics

Exit condition: every mechanism has source-backed semantics, positive
theorems, independence/non-collapse theorems, and finite or semantic
countermodels.

For each M1-M12:

1. Source-backed prose definition.
2. Typed semantic profile.
3. Satisfaction predicate.
4. Warrant classification.
5. Positive projection theorem family.
6. Independence from every non-identical mechanism or documented dependency.
7. Countermodels for unsafe entailments.
8. Relation to ISF and M8.

Current status: M8 partial; M1-M7 and M9-M11 are mostly labels.
Source-resource update: mechanism names and workbook accepted/pending status
are now encoded in Lean.  Full source-backed semantics remain open because the
available resources do not provide enough detail to derive them without
invention.

## Lane E - Contradiction, Insight, And Delta Dynamics

Exit condition: contradiction and Delta are operational, not merely taxonomic.

1. Frame histories.
2. Transition systems.
3. Delta classifier rules.
4. Outcome exclusivity/overlap theorems relative to policies.
5. Outcome incompleteness/coverage theorems.
6. Higher-order defeater dynamics.
7. Non-finality and non-truth robustness under histories.

Current status: MC3-Lean finite transition artifacts now exist in Lane K for
Delta reachability, non-finality, terminal stability, modal eventuality, and a
non-resolution loop counterexample.  The full operational Delta classifier
program above remains open.

## Lane F - Evaluator Calculus

Exit condition: evaluator acceptance is calibrated and reliability-aware, not
only criteria-relative by supplied fields.

1. Evaluator scoring functions.
2. Decision procedures.
3. Error models.
4. Calibration definitions.
5. Inter-evaluator disagreement.
6. Aggregation rules.
7. Soundness/completeness for declared evaluator fragments.
8. Empirical reliability linkage.

Current status: MC3-Lean plus ECC-bounded executable checking for a finite
score/decision fragment.  `EvaluatorCalibration.lean` defines three score
levels, threshold decisions, disagreement witnesses, and a three-evaluator
majority rule.  `python/evaluator_calibration_check.py` exhaustively checks all
27 three-score triples.  Empirical reliability, calibrated real-world scoring
rubrics, and external validation remain open.

## Lane G - Normative Bridge And Repair

Exit condition: every bridge warrant is externally sourced or explicitly
unjustified; repair stages have defeaters, regress, externality, closure, and
non-collapse families.

1. Bridge-specific warrant sources.
2. Defeater taxonomy.
3. Domain standards for harm, responsibility, repair, accountability, legal
   illegitimacy, governance legitimacy, and moral guilt.
4. Repair closure and regress theorem families.
5. Bridge independence countermodel families beyond one-element witnesses.

Current status: SCAF.

## Lane H - Executable Checking

Exit condition: executable artifacts are regression-tested, generated from or
proved against formal specifications, and coverage is honest.

1. Pytest coverage for finite checker.
2. Pytest coverage for proof checker.
3. Shared target specification or Lean/Python correspondence proof.
4. Larger bounded finite search.
5. Coverage ledger.
6. Negative tests for malformed proof traces.

Current status: EFC/PYC/GRC/DLC/RRC/ECC/PPC scaffold with pytest regression
coverage for checker logic and persisted artifacts.  Bounded sweeps now cover
finite target implications, proof traces, propositional proof targets,
granularity refinement, Delta transition systems, repair revision, and
evaluator calibration.  Formal Lean/Python correspondence and larger global
search remain open.

## Lane I - Empirical Program

Exit condition: empirical validation claims reach EMP4 or are not made.

1. Pilot cases selected.
2. Pilot coded.
3. Reliability computed.
4. Coding manual revised.
5. Construct-validity review.
6. Independent replication.
7. Empirical limitations and claim packet.

Current status: EMP0.

## Lane J - Academic Review And Publication

Exit condition: external review is received and revisions are made.

1. Literature review expansion.
2. Reducibility responses.
3. Reviewer packet sent.
4. Reviewer comments recorded.
5. Revisions completed.
6. Claim packet revised.
7. Publication-ready statement.

Current status: EXT0.

## Lane K - Novel Mathematical Discovery

Exit condition: novel research directions are converted into checked
definitions, theorems, countermodels, executable tests, or empirical protocols.

1. Contextual obstruction semantics.
2. Institution-theoretic signature change.
3. Coalgebraic Delta dynamics.
4. Belief-revision and minimal-repair calculus.
5. Argumentation/evaluator semantics.
6. Rough-set and formal-concept approximations for evidence adequacy.

Current status: active.  Contextual obstruction has an MC3-Lean exploratory
core with positive and obstructed regression examples.  Delta dynamics has an
MC3-Lean finite transition core with positive reachability and a liveness
counterexample.  Minimal repair has an MC3-Lean preferential core with a
non-uniqueness counterexample, a ranked repair-revision fragment separating
targeted repair from under-repair and over-repair, and an RRC-bounded sweep of
256 action-result maps, plus finite postulate-independence witnesses.
Argumentation has an MC3-Lean evaluator-defense
core with conflict-free-but-not-admissible and evaluator-accepted-but-not-
defended counterexamples, and evaluator calibration has a finite score,
disagreement, and majority-rule fragment with an ECC-bounded 27-triple sweep.
Rough evidence has an MC3-Lean approximation core
separating possible support from definite adequacy eligibility, and rough
lower approximation is now connected to adequacy-profile sufficiency.  It also
has an MC3-Lean granularity layer proving lower approximation is preserved by
relation refinement, plus a finite converse-failure case where coarse evidence
blocks rough adequacy while identity-level granularity restores eligibility
for the favorable item.  It also has an MC3-Lean formal-concept fragment with
a Galois connection and evidence concept example, plus a narrow M7
concept-attribution blocker based on missing concept intent.  Other directions
are mapped in `docs/NOVELTY_RESEARCH_LANES.md`.
Institution-style local logic fragments now have an MC3-Lean
satisfaction-condition interface and a non-preservation counterexample.

## Immediate Execution Queue

1. Finish Lane A.
2. Finish Lane H regression tests.
3. Extend Lane C from positive quantifier-free isomorphism equivalence toward
   general-formula preservation boundaries and finite-search coverage.
4. Begin Lane B quantified derivability and completeness boundary work.
5. Begin Lane K contextual obstruction and other novelty lanes with real
   formal tests.
6. Begin Lane D mechanism semantics, one mechanism at a time.

## External Blockers

The following cannot be completed locally without new external input:

- EMP1-EMP4 empirical statuses.
- EXT1-EXT3 review statuses.
- Publication acceptance.

All local formal, executable, and documentation work continues until those
become the only remaining blockers.
