# M11 Symbolic Overload Check Report - 2026-06-11

Status: `M11C-pass`.

This report records the M11 mechanism-specific deepening pass.  M11 is
formalized as symbolic overload: one symbolic output carries multiple material
interpretations, those interpretations conflict, and disambiguation,
evaluator-resolution, and boundary controls are missing.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/SymbolicOverload.lean`
- Executable checker:
  - `python/symbolic_overload_check.py`
- Persisted outputs:
  - `docs/symbolic_overload_checks/coverage.json`
  - `docs/symbolic_overload_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `SymbolicOverloadProfile`;
- `SymbolicOverloadProfileSatisfied`;
- `SymbolicOverloadProfileBlocked`;
- conversion from a satisfied M11 profile to `SupportDegradedSem`;
- conversion from a satisfied M11 profile to a generic `ISFTMechanismProfile`
  labelled `M11`;
- `M11SymbolicOverloadCase`;
- conversion from a satisfied M11 symbolic-overload case to `ISFSem`.

## Required Conditions

The checker confirms all eight required M11 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- symbol declared;
- multiple interpretations present;
- interpretations conflict;
- audience uptake material;
- claim depends on overloaded symbol;
- disambiguation absent;
- evaluator resolution absent;
- boundary guard absent.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M11 from collapsing into a generic
symbolic-complexity complaint with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M11 and is not a source-complete
semiotic theory.  It is a Lean-checked operational profile for the M11
candidate mechanism, with executable coverage checks and explicit blockers.
