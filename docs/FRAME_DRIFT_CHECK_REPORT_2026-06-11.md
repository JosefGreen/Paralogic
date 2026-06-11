# M10 Frame Drift Check Report - 2026-06-11

Status: `M10C-pass`.

This report records the M10 mechanism-specific deepening pass.  M10 is
formalized as frame drift: a claim is carried from a declared source frame to a
target frame while material context conditions have changed and continuity or
boundary controls are missing.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/FrameDrift.lean`
- Executable checker:
  - `python/frame_drift_check.py`
- Persisted outputs:
  - `docs/frame_drift_checks/coverage.json`
  - `docs/frame_drift_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `FrameDriftProfile`;
- `FrameDriftProfileSatisfied`;
- `FrameDriftProfileBlocked`;
- conversion from a satisfied M10 profile to `SupportDegradedSem`;
- conversion from a satisfied M10 profile to a generic `ISFTMechanismProfile`
  labelled `M10`;
- `M10FrameDriftCase`;
- conversion from a satisfied M10 frame-drift case to `ISFSem`;
- a directional frame-change witness for the positive case.

## Required Conditions

The checker confirms all eight required M10 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- source frame declared;
- target frame used;
- frame shift present;
- claim carried across frames;
- context conditions changed;
- material drift;
- continuity guard absent;
- boundary guard absent.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M10 from collapsing into a generic
context-change complaint with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M10 and is not a source-complete
framing theory.  It is a Lean-checked operational profile for the M10
candidate mechanism, with executable coverage checks and explicit blockers.
