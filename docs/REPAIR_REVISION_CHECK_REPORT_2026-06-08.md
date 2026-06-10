# Repair Revision Check Report - 2026-06-08

Status: RRC-bounded pass.

This checker mirrors the finite ranked-repair fragment in
`src/Paralogic/MinimalRepair.lean`.

## Scope

- states checked: `unrepaired`, `underRepaired`, `adequate`, `overRepaired`
- actions checked: `noAction`, `partialAction`, `targetedAction`,
  `excessiveAction`
- action-result maps checked: 256
- action evaluations checked: 1024
- minimal acceptable states found: `adequate`

## Main Bounded Result

For every checked action-result map, an action satisfies all repair-revision
postulates exactly when its result is `adequate`.

There were zero postulate-equivalence failures.

Lean also proves `best_acceptable_unique_minimal`, an abstract theorem: in an
antisymmetric preference frame, a selected acceptable state that is at least as
preferred as every acceptable candidate is the unique minimal repair.  The
checker verifies the finite ranked-frame hypotheses used by
`rankedRepair_unique_minimal_from_best`; it does not prove the abstract theorem.

## Postulate Independence Table

A second finite frame checks that the postulates do not collapse into one
another:

- `adequateAction` satisfies success, minimality, and conservatism.
- `redundantAction` satisfies success and conservatism but fails minimality.
- `overreachAction` satisfies success and minimality but fails conservatism.
- `failedAction` satisfies conservatism but fails success.

The independence table status is `RRC-independence-pass`.

## Negative Controls

- `partialAction` and `noAction` fail success.
- `excessiveAction` succeeds in the weak acceptability sense but fails
  minimality and conservatism.
- 256 successful-but-not-postulate action evaluations were found.
- 256 overrepair-success-but-not-postulate action evaluations were found.

## Anti-Overclaim Guard

This is a bounded finite checker.  It does not prove general AGM revision
theorems, does not validate any external repair obligation standard, and does
not show that the ranked order is uniquely correct.  It tests the local finite
ranked-repair semantics against the Lean witnesses and records the boundary
between targeted repair, under-repair, and over-repair.

## Artifacts

- `python/repair_revision_check.py`
- `docs/repair_revision_checks/action_table.json`
- `docs/repair_revision_checks/postulate_independence_table.json`
- `docs/repair_revision_checks/postulate_independence_summary.json`
- `docs/repair_revision_checks/sweep_summary.json`
- `docs/repair_revision_checks/lean_named_witnesses.json`
- `docs/repair_revision_checks/coverage.json`
