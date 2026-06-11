# M3 Formal Access Check Report - 2026-06-11

Status: `M3C-pass`.

This report records the M3 mechanism-specific deepening pass.  M3 is
formalized as formal-access substitution: an institution treats nominal or
procedural access as substantive access even though effective usability,
comprehension, remedy, and boundary conditions are missing.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/FormalAccessSubstitution.lean`
- Executable checker:
  - `python/formal_access_check.py`
- Persisted outputs:
  - `docs/formal_access_checks/coverage.json`
  - `docs/formal_access_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `FormalAccessProfile`;
- `FormalAccessProfileSatisfied`;
- `FormalAccessProfileBlocked`;
- conversion from a satisfied M3 profile to `SupportDegradedSem`;
- conversion from a satisfied M3 profile to a generic `ISFTMechanismProfile`
  labelled `M3`;
- `M3FormalAccessSubstitutionCase`;
- conversion from a satisfied M3 access-substitution case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M3 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- formal access declared;
- substantive access absent;
- access treated as sufficient;
- material usability barrier;
- material comprehension barrier;
- absent remedy path;
- absent boundary guard.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M3 from collapsing into a generic
access complaint or support-degradation label with no formal boundary.

## Boundary

This pass is not an empirical validation of M3 and is not a source-complete
literature review.  It is a Lean-checked operational profile for the M3
candidate mechanism, with executable coverage checks and explicit blockers.

