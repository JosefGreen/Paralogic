# Granularity Check Report - 2026-06-08

Status: GRC-pass.

Scope: bounded executable check over the three-item rough-evidence universe
`{favorable, corroborating, unfavorable}` with fixed support labels:

- `favorable` supports the target;
- `corroborating` supports the target;
- `unfavorable` does not support the target.

The checker enumerates all reflexive granularity relations on the three-item
universe, then checks every refinement pair.  A fine relation refines a coarse
relation when every fine indistinguishability pair is also a coarse
indistinguishability pair.

Artifacts:

- `python/granularity_check.py`
- `src/Paralogic/EvidenceGranularity.lean`
- `docs/granularity_checks/coverage.json`
- `docs/granularity_checks/converse_failures.json`
- `docs/granularity_checks/lean_named_witnesses.json`
- `docs/granularity_checks/summary.json`

Results:

- relation count: 64
- refinement cases checked: 2187
- refinement-law failures: 0
- converse-failure witnesses: 486
- Lean-named witnesses checked against generated witnesses: 1
- missing Lean-named witnesses: 0

Claim warranted by this checker:

- In this bounded universe, lower approximation under a coarse relation is
  preserved under every relation refinement.
- The Lean layer now mirrors the six optional ordered off-diagonal relation
  fields with `ThreeGranularityMask` and checks the 64-mask count.
- The checker now persists a Lean-named witness payload for
  `mask_payload_converse_failure` and verifies that this payload appears among
  the generated converse-failure witnesses.

Claim explicitly not warranted by this checker:

- This does not prove empirical adequacy.
- This does not prove the theorem for arbitrary universes; the general result
  is checked separately in Lean as
  `lower_preserved_under_relation_refinement`.
- This does not decide source-backed M7 mechanism semantics.
