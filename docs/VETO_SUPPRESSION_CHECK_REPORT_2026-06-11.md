# M9 Veto Suppression Check Report - 2026-06-11

Status: `M9C-pass`.

This report records the M9 mechanism-specific deepening pass.  M9 is
formalized as veto suppression: a veto or blocking right is declared or
procedurally available, an affected participant attempts to use it, but the
attempt is materially suppressed while review and boundary conditions are
missing.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/VetoSuppression.lean`
- Executable checker:
  - `python/veto_suppression_check.py`
- Persisted outputs:
  - `docs/veto_suppression_checks/coverage.json`
  - `docs/veto_suppression_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `VetoSuppressionProfile`;
- `VetoSuppressionProfileSatisfied`;
- `VetoSuppressionProfileBlocked`;
- conversion from a satisfied M9 profile to `SupportDegradedSem`;
- conversion from a satisfied M9 profile to a generic `ISFTMechanismProfile`
  labelled `M9`;
- `M9VetoSuppressionCase`;
- conversion from a satisfied M9 veto-suppression case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M9 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- veto right declared;
- affected participant present;
- veto attempt made;
- veto suppressed;
- material suppression;
- review path absent;
- boundary guard absent.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M9 from collapsing into a generic
participation complaint with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M9 and is not a source-complete
governance theory.  It is a Lean-checked operational profile for the M9
candidate mechanism, with executable coverage checks and explicit blockers.

