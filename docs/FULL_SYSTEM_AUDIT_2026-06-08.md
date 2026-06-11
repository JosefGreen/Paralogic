# Full System Audit - 2026-06-08

Verdict: incomplete.

The repository is useful and now builds, but it is not an exhaustively
developed mathematical system.  Its current status is best described as a
Lean-checked scaffold plus selected countermodels, bounded executable checks,
PYC proof traces, EMP0 protocol documents, and internal review artifacts.

## Verification Performed

- Lean build: passed with Lean 4.19.0.
- `python/finite_check.py`: passed 10 bounded finite targets.
- `python/proof_check.py`: PYC-pass on 8 rules and 6 traces.
- `python/granularity_check.py`: GRC-pass on 64 three-item reflexive
  relations and 2187 refinement cases.
- `python/delta_check.py`: DLC-pass with two-state and three-state exhaustive
  sweeps.
- `python/repair_revision_check.py`: RRC-pass on 256 action-result maps and
  1024 action evaluations.
- `python/evaluator_calibration_check.py`: ECC-pass on 27 three-evaluator
  score triples.
- `python/propositional_proof_check.py`: PPC-pass on seven propositional
  proof-theory targets.
- `python -m pytest -q`: passed 34 regression tests after adding checker and
  persisted-artifact tests.
- Overclaim scan: no active `sorry`, `admit`, or `unsafe`; scan hits are mostly
  caveats, anti-claims, and status labels.

## Immediate Fix Applied

`src/Paralogic/CoreTypes.lean` claimed `predicateSymbolCount := 32`, while
`src/Paralogic/ModelSemantics.lean` defines 29 predicate-symbol constructors.
The count is now corrected to 29, with checked count theorems added.

`python/tests/test_checkers.py` now exercises the bounded finite checker,
custom proof checker, bounded granularity checker, bounded Delta checker,
bounded repair-revision checker, bounded evaluator-calibration checker,
bounded propositional proof checker, negative proof-trace cases, and persisted
coverage / witness / trace artifacts.  This moves the old "no tests ran"
finding into a repaired state, but does not make the executable checkers
globally exhaustive.

## Major Findings

### F1 - Completion Language Is Too Strong

`docs/COMPLETION_PIPELINE.md` says the scoped pass is finished and repeatedly
marks gates as closed.  This is at risk of reward hacking.  A scoped artifact
pass is not the same as completion of Paralogic, ISFT, model theory, empirical
validation, or academic review.

Required repair:

- Replace "closed" language with graded status labels.
- Track each gate as `scaffolded`, `partially proved`, `bounded checked`,
  `externally reviewed`, or `validated`.

### F2 - Theorem Ledger Inflates Definitional Projections

Many ledger entries are real Lean artifacts, but a large fraction are
projection theorems, blocker constructors, or one-step consequences of
structure fields.  They should not be presented as deep mathematical results.

Required repair:

- Split the theorem ledger into projection lemmas, structural lemmas,
  countermodels, executable artifacts, and substantive theorems.
- Add a "depth/risk" column.

### F3 - Many Warrants Are Fields, Not Derived Theorems

Normative, empirical, adequacy, evaluator, contradiction, suppression, power,
and repair modules often include a `warrant` field and then prove that if the
warrant is supplied, the conclusion follows.  This is type-correct but not a
derivation of the warrant.

Required repair:

- Create an axiom/warrant audit.
- For each warrant, classify it as primitive, externally justified,
  empirically testable, or still unsupported.
- Do not count warrant-consuming theorems as independent validation.

Partial repair applied: `WarrantDischarge.lean` now enumerates current
warrant-like obligations, classifies them as countermodel-guarded, proves they
are not yet source-backed or empirically validated, and gives all-false-model
countermodels against treating raw profile conditions as sufficient for the
warranted conclusion.  This accounts for the obligations but does not discharge
them into source-backed or empirical status.
Additional repair applied: adequacy now has a scoped operational discharge
model in which `adequate` is computed from supported evidence, in-scope
context, and matched claim, with an unsupported-evidence negative control. This
is still not empirical validation or an external source-backed adequacy theory.
Additional repair applied: evaluator accepting decisions now have a scoped
operational discharge model connecting high-score acceptance to
`EvaluatorAcceptsSem` for an approved evaluator/candidate pair, while low-score
acceptance remains blocked. This is still not empirical evaluator calibration.
Additional repair applied: evaluator criteria now have a scoped operational
discharge profile connecting declared, relevant, inspected, applied, and
no-error criteria to `EvaluatorAcceptsSem` for the same approved
evaluator/candidate pair. This is still not source-backed evaluator policy or
empirical reliability.
Additional repair applied: contradiction presence now has a scoped operational
discharge model in which an active frame, active context, and contested claim
compute `ContradictionPresentSem`, with resolved-claim, inactive-frame, and
inactive-context negative controls. This is still not a source-backed or
empirically validated contradiction taxonomy.
Additional repair applied: M8 power-condition relevance, validity dependence,
and omission now have a scoped operational discharge model with negative
controls for unaffected group, immaterial power condition, and ordinary output.
This is still not an external institutional case analysis or empirical power
study.
Additional repair applied: suppression support-degradation now has a scoped
operational discharge model with negative controls for unsupported evidence,
mismatched context, and ordinary claim. This is still not empirical evidence
that suppression has occurred in any concrete case.
Additional repair applied: repair obligation now has a scoped operational
discharge model with negative controls for ordinary bridge, other institution,
and other group. This is still not external legal, moral, governance, or
empirical justification.
Additional repair applied: full empirical validation now has a protocol-level
operational discharge model requiring validation, construct-validity,
reliability, and replication predicates, with negative controls for nominal
validation, unvalidated objects, and other claims. This is still not real
empirical data, computed reliability, construct-validation study, or
replication.
Additional repair applied: normative bridges now have a conclusion-indexed
operational discharge model with distinct bridge tokens for harm,
responsibility, repair obligation, accountability, legal illegitimacy,
governance legitimacy, and moral guilt. This is still not external legal,
moral, governance, or institutional authority.

### F4 - One-Element Witnesses Are Useful But Too Weak

Many non-collapse theorems use `UnitPredicateModel` or one-object `World`
witnesses.  They are valid countermodels for narrow non-entailment claims, but
they do not establish robustness under richer carrier structure, morphisms,
domains, temporal dynamics, or empirical constraints.

Required repair:

- Add finite models with at least two elements in relevant sorts.
- Add parameterized countermodel families.
- Add tests showing non-collapse survives under nontrivial functions and
  predicate interpretations.

Partial repair applied: `FrameContext.lean` now proves pointwise associativity
for model-hom composition, preservation of term and argument evaluation under
mapped assignments, and preservation of positive quantifier-free formula
satisfaction.  This does not cover negation, implication, quantifiers, or
general formula translation preservation.

Additional boundary repair applied: `NonPreservation.lean` now contains
checked counterexamples showing that a model homomorphism need not preserve
negation, implication, or universal quantification.  These witnesses justify
the positive-fragment restriction instead of leaving it as an informal caveat.

Additional partial repair applied: `FrameContext.lean` now defines model
isomorphisms with forward/backward homomorphisms, identity, composition,
predicate reflection, assignment-update transport across inverse carrier
maps, and full formula satisfaction equivalence.  This is a genuine
isomorphism theorem; it does not weaken the separate counterexamples showing
that ordinary one-way homomorphisms fail on negation, implication, and
universal quantification.

Additional partial repair applied: formula translations now have identity and
composition operations, plus one-way preservation of satisfied premise lists.
They also transport a source instance of a global semantic entailment through
a satisfaction-preserving translation.  This still does not prove reflection,
equivalence of translations, or unrestricted target-side semantic entailment
for arbitrary target assignments.

Partial repair applied: `NontrivialFiniteModels.lean` adds Bool carriers for
every sort, finite carrier witnesses with two elements, and representative
two-element non-collapse witnesses for `UsesSem not-> ISFSem` and
`ISFSem not-> M8Sem`.

### F5 - M1-M12 Are Mostly Labels

`ISFTMechanisms.lean` defines M1-M12 labels and generic profiles, but only M8
has partial semantic content through power-erasure profiles.  M1-M7 and M9-M11
remain source-backed future work, not developed mechanisms.

Required repair:

- Define each mechanism's semantics.
- Define dependencies and independence for each mechanism.
- Add countermodels showing mechanisms do not collapse into each other.
- Add source-grounded descriptions before formalization.

Partial repair applied: source-resource audit found official mechanism names
and workbook accepted/pending status.  These are now encoded in Lean as
`mechanismName`, `WorkbookMechanismStatus`, and associated accepted/pending
theorems.  The audit did not find enough semantic detail to complete
source-backed formal semantics for all mechanisms without invention.
Additional repair applied: `MechanismSynthesis.lean` now adds a
candidate-synthesized semantics tier for M1-M12.  Each candidate definition has
an explicit maturity status, academic lens, failure axis, operational trigger,
boundary guard, empirical coding plan, and non-collapse guard.  Lean theorems
separate candidate-synthesized status from source-backed and empirically
validated status.

### F6 - Formula/Model Theory Is Still Thin

The many-sorted syntax has terms, formulas, substitution, satisfaction, and
some foundation lemmas.  It still lacks a mature proof theory, completeness or
soundness theorem for a calculus, alpha-equivalence, full capture-avoiding
substitution for quantified formulas, structure-level category laws, and
robust translation/projection laws.

Required repair:

- Define derivability and prove soundness against `SatisfiesFormula`.
- Add alpha-equivalence and stronger substitution lemmas.
- Complete model-hom identity/associativity laws at the structure level.
- Prove formula translation preservation conditions beyond records.

Additional foundation repair applied: `FoundationLemmas.lean` now proves that
agreement on all free variables induces formula agreement, and that closed
formulas and closed premise lists are invariant under arbitrary assignment
changes.  This tightens the semantic hygiene needed before alpha-equivalence
and eigenvariable machinery.

Partial repair applied: `ProofTheory.lean` now has soundness for a larger
natural-deduction fragment, including implication introduction, falsity
elimination, disjunction elimination, universal current-value elimination, and
existential current-value introduction.  It also includes universal
introduction under semantic premise-stability, with stability-aware
derivation weakening.  Quantifier-free syntactic freshness now implies
assignment-update stability, allowing a bounded class of universal-introduction
side conditions to be discharged from no-free-variable facts.
Additional repair applied: full syntactic no-free-variable freshness now
implies assignment-update stability, including quantified binder-shadowing
cases, so universal-introduction side conditions can be discharged for a
larger formula class than the quantifier-free fragment.
Additional repair applied: direct semantic universal-introduction theorems now
match the derivability rule under premise stability, quantifier-free freshness,
and full no-free-variable freshness.
Boundary repair applied: `NonPreservation.lean` now contains a semantic
countermodel showing that unrestricted universal introduction from a premise
with the generalized variable free is not valid.  This confirms that the
freshness/stability side condition is a live mathematical constraint, not a
cosmetic guard.
`python/propositional_proof_check.py`
truth-table checks seven positive and negative propositional targets.  Full
quantified proof theory with syntactic freshness/eigenvariable conditions and
completeness remains open.

### F7 - Delta And Insight Are Taxonomic, Not Operational

Delta outcomes and insight cases are typed and guarded, but there is no
operational classifier, transition semantics over histories, or proof that
Delta outcomes are complete or mutually exclusive under realistic policies.

Required repair:

- Define frame histories and transition systems.
- Define classifier rules for each Delta outcome.
- Prove exclusivity, overlap, and incompleteness theorems against those rules.

### F8 - Evaluator Calculus Is Criteria-Relative But Not Epistemically Strong

Evaluator modules separate acceptance, rejection, abstention, error, and
incompleteness.  However, criteria soundness/completeness are supplied as
fields.  No external evaluator behavior, scoring function, calibration, or
inter-evaluator reliability exists.

Partial repair applied: `EvaluatorCalibration.lean` now defines a finite
score-to-decision procedure, disagreement predicates, and a three-evaluator
majority aggregation rule.  `python/evaluator_calibration_check.py` exhaustively
checks all 27 three-score triples.  This is still not empirical calibration or
inter-rater reliability.

Required repair:

- Define evaluator scoring and decision procedures.
- Add calibration/error models.
- Add inter-evaluator disagreement and aggregation semantics.
- Connect to empirical reliability artifacts.

### F9 - Repair And Normative Bridges Are Schemas, Not Normative Proofs

Repair stages and bridge schemas are explicit, which is good.  But the bridge
warrants are not legally, morally, institutionally, or empirically justified.

Partial repair applied: `MinimalRepair.lean` now includes a ranked finite
repair-revision frame, positive and negative repair-action postulate tests,
finite postulate-independence witnesses, and a concrete diagnosis-guided
targeted repair witness.  The bridge conclusion remains conditional on
`RepairDiagnosisProfile.warrantRepairObligation`.

Required repair:

- Add bridge-specific warrant sources.
- Add domain standards for harm, responsibility, accountability, legality,
  governance legitimacy, moral guilt, and repair obligation.
- Add defeater taxonomies and examples.

### F10 - Executable Finite Checking Is Bounded And Separate From Lean

The finite checker enumerates target-relevant Boolean atoms for 10 targets.  It
does not search the full many-sorted model space, and the Python checker is not
proved sound in Lean.

Required repair:

- Add a formal spec for the finite-check target language.
- Prove correspondence between Python targets and Lean formulas, or generate
  both from a shared source.
- Add global or systematically bounded model search with coverage accounting.
- Add normal Python tests.

### F11 - The PYC Checker Is Tiny

The proof checker handles a small Horn-like fragment with 8 rules and 6 traces.
It is useful as an independent sanity check, but it is not a proof assistant or
a verifier for the Lean development.

Partial repair applied: regression tests now verify accepted traces, rejected
traces, unknown-rule rejection, invalid-reference rejection, and persisted
proof-check artifact consistency.

Required repair:

- Add a formal grammar for proof traces.
- Add negative tests for malformed references, unknown rules, cycles, and
  invalid conclusions.
- Add a larger generated trace suite from the theorem ledger.

### F12 - Empirical Status Is Still EMP0

The empirical directory contains protocols, not data.  There are no coded
cases, reliability statistics, construct-validity study, pilot results, or
replication artifacts.

Required repair:

- Run a pilot study.
- Record coder data.
- Compute reliability.
- Revise constructs.
- Obtain independent replication before validation claims.

### F13 - Academic Review Has Not Happened

The academic folder contains internal comparison artifacts.  It does not
contain peer review, expert review, publication review, or a completed
literature survey.

Required repair:

- Send the external review packet.
- Record reviewer identity/expertise, date, comments, and revisions.
- Expand literature coverage beyond the initial anchors.

### F14 - Documentation Drift Is Serious

Older audit documents still say some artifacts do not exist, while newer
documents say scoped gates are finished.  Both can be defensible historically,
but the repo lacks a current canonical status page that supersedes stale
documents.

Required repair:

- Create `docs/CURRENT_STATUS.md`.
- Mark older documents as historical snapshots.
- Ensure README, gap ledger, theorem ledger, and pipeline agree.

## Correct Current Status

Use this wording:

> The repository contains Lean-checked scaffold modules, selected
> non-collapse countermodels, bounded finite-check artifacts, bounded
> granularity, Delta, repair-revision, and evaluator-calibration checkers, a
> tiny custom proof checker, a bounded propositional proof checker, EMP0
> empirical protocols, and internal academic-audit documents.  It is not a
> complete mathematical system and is not empirically validated.

## Priority Remediation Pipeline

1. Documentation reset: create a canonical current-status page and demote
   "closed" gate language.
2. Warrant audit: classify every warrant field and remove theorem-ledger
   inflation.
3. Signature consistency: connect `CoreTypes.Signature` counts to actual
   enumerations in Lean.
4. M1-M12 semantics: define source-backed semantics for every mechanism.
5. Proof theory: define derivability and prove soundness.
6. Nontrivial model families: replace one-element-only witnesses with richer
   families.
7. Delta operationalization: define transition systems and classifier rules.
8. Evaluator calibration: define scoring, disagreement, reliability, and
   aggregation.
9. Executable checking: connect Python artifacts to Lean formulas or shared
   target specs.
10. Empirical pilot and external review.
