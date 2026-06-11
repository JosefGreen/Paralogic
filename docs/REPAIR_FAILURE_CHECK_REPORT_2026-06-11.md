# M5 Repair Failure Check Report - 2026-06-11

Status: `M5C-pass`.

This report records the M5 mechanism-specific deepening pass.  M5 is
formalized as repair failure: a repair need is present, responsibility is
identified, but planning, action, verification, recurrence control, or closure
conditions fail while the institution still treats the output as adequate.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/RepairFailure.lean`
- Executable checker:
  - `python/repair_failure_check.py`
- Persisted outputs:
  - `docs/repair_failure_checks/coverage.json`
  - `docs/repair_failure_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `RepairFailureProfile`;
- `RepairFailureProfileSatisfied`;
- `RepairFailureProfileBlocked`;
- conversion from a satisfied M5 profile to `SupportDegradedSem`;
- conversion from a satisfied M5 profile to a generic `ISFTMechanismProfile`
  labelled `M5`;
- `M5RepairFailureCase`;
- conversion from a satisfied M5 repair-failure case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M5 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- repair need declared;
- responsible agent identified;
- repair plan absent;
- repair action failed;
- verification absent;
- material recurrence;
- closure claim maintained.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M5 from collapsing into a generic
complaint about failed repair with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M5 and is not a source-complete
repair theory.  It is a Lean-checked operational profile for the M5 candidate
mechanism, with executable coverage checks and explicit blockers.

