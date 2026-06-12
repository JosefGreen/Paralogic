# Theorem Depth Ledger

## Purpose

This ledger separates useful formal results from low-depth projections,
bookkeeping lemmas, bounded checks, operational schemas, and open gaps.

CSV: `docs/ledgers/theorem_depth_ledger.csv`.

## Scope

This is a benchmark review ledger, not a complete inventory of every Lean
declaration. Baseline extraction found many theorem/example declarations and
many definitions/structures. The ledger classifies representative high-risk
and public-facing items first, because those are most likely to be overclaimed.

## Depth Taxonomy

- D0_DEF_EQ_PROJECTION: immediate field/projection/constructor/rfl result.
- D1_STRUCTURAL: internal infrastructure lemma.
- D2_COUNTERMODEL: witness blocking entailment, collapse, or preservation.
- D3_EXECUTABLE_CHECK_LINKED: tied to bounded Python checker or artifact.
- D4_SUBSTANTIVE_FORMAL: nontrivial formal result over project objects.
- D5_SOUNDNESS_OR_META: proof-theoretic or semantic meta-theoretic result.
- D6_OPERATIONAL_SCHEMA: scoped operational model, not empirical validation.
- D7_DOCUMENTATION_OR_PROTOCOL: documentation or protocol.
- D8_OPEN_GAP: missing theorem or future work.

## Risk Taxonomy

- R0_SAFE_FOUNDATIONAL
- R1_SAFE_BUT_LOW_DEPTH
- R2_BOUNDARY_DEPENDENT
- R3_WARRANT_CONDITIONAL
- R4_BOUNDED_ONLY
- R5_SOURCE_BACKING_MISSING
- R6_EMPIRICAL_MISSING
- R7_EXTERNAL_REVIEW_MISSING
- R8_OVERCLAIM_RISK

## Key Classification Findings

- Projection theorems such as `ISF_to_Uses` are useful but low-depth.
- Non-collapse countermodels are practically important because they block
  false public inferences.
- Bounded checker links improve reproducibility but do not produce global
  proof.
- Operational schemas can be useful claim-boundary tools but are not empirical
  validation.
- D4/D5 classifications require extra caution and should be reviewed first.

## Reviewer Questions

1. Are any D4/D5 classifications too generous?
2. Are D0 projections being described as substantive in public text?
3. Are bounded checker links being mistaken for global proof?
4. Are warrant-dependent projections clearly marked?

## Usefulness Check

The ledger helps a reviewer inspect formal depth faster and blocks theorem
count inflation. It does not replace source review of the Lean files.

## Claim Boundary

This ledger does not prove that the theorem inventory is complete, that the
system is complete, or that any result has empirical or external-review status.
