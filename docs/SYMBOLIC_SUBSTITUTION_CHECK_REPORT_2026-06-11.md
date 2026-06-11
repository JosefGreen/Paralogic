# M4 Symbolic Substitution Check Report - 2026-06-11

Status: `M4C-pass`.

This report records the M4 mechanism-specific deepening pass.  M4 is
formalized as symbolic substitution: an institution treats a symbol, label, or
representation as a substantive condition even though fit, material grounding,
correction, and boundary conditions are missing.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/SymbolicSubstitution.lean`
- Executable checker:
  - `python/symbolic_substitution_check.py`
- Persisted outputs:
  - `docs/symbolic_substitution_checks/coverage.json`
  - `docs/symbolic_substitution_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `SymbolicSubstitutionProfile`;
- `SymbolicSubstitutionProfileSatisfied`;
- `SymbolicSubstitutionProfileBlocked`;
- conversion from a satisfied M4 profile to `SupportDegradedSem`;
- conversion from a satisfied M4 profile to a generic `ISFTMechanismProfile`
  labelled `M4`;
- `M4SymbolicSubstitutionCase`;
- conversion from a satisfied M4 symbolic-substitution case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M4 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- symbol declared;
- symbol treated as substantive;
- representation mismatch;
- material condition absent;
- material audience uptake;
- absent correction path;
- absent boundary guard.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M4 from collapsing into a generic
symbolic critique with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M4 and is not a source-complete
literature review.  It is a Lean-checked operational profile for the M4
candidate mechanism, with executable coverage checks and explicit blockers.

