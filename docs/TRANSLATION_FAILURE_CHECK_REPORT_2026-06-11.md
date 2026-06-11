# M6 Translation Failure Check Report - 2026-06-11

Status: `M6C-pass`.

This report records the M6 mechanism-specific deepening pass.  M6 is
formalized as translation failure: a translation between source and target
contexts is treated as adequate even though semantic loss, broken linkage,
verification absence, and boundary failure degrade support.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/TranslationFailure.lean`
- Executable checker:
  - `python/translation_failure_check.py`
- Persisted outputs:
  - `docs/translation_failure_checks/coverage.json`
  - `docs/translation_failure_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `TranslationFailureProfile`;
- `TranslationFailureProfileSatisfied`;
- `TranslationFailureProfileBlocked`;
- conversion from a satisfied M6 profile to `SupportDegradedSem`;
- conversion from a satisfied M6 profile to a generic `ISFTMechanismProfile`
  labelled `M6`;
- `M6TranslationFailureCase`;
- conversion from a satisfied M6 translation-failure case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M6 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- source context declared;
- target context declared;
- translation performed;
- material semantic loss;
- broken actor link;
- verification absent;
- boundary guard absent.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M6 from collapsing into a generic
translation complaint with no formal support-degradation boundary.

## Boundary

This pass is not an empirical validation of M6 and is not a source-complete
translation theory.  It is a Lean-checked operational profile for the M6
candidate mechanism, with executable coverage checks and explicit blockers.

