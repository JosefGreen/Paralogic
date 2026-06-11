# M1 Evidence Overclaim Check Report - 2026-06-11

Status: `M1C-pass`.

This report records the M1 mechanism-specific deepening pass.  M1 is
formalized as evidence overclaim: an institution treats a claim as adequately
supported even though the available evidence is relevant but insufficient,
scope-mismatched, uncertainty-exposed, and materially overextended.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/EvidenceOverclaim.lean`
- Executable checker:
  - `python/evidence_overclaim_check.py`
- Persisted outputs:
  - `docs/evidence_overclaim_checks/coverage.json`
  - `docs/evidence_overclaim_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `EvidenceOverclaimProfile`;
- `EvidenceOverclaimProfileSatisfied`;
- `EvidenceOverclaimProfileBlocked`;
- conversion from a satisfied M1 profile to `SupportDegradedSem`;
- conversion from a satisfied M1 profile to a generic `ISFTMechanismProfile`
  labelled `M1`;
- `M1EvidenceOverclaimCase`;
- conversion from a satisfied M1 overclaim case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M1 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- claim scope declared;
- evidence relevant;
- evidence insufficient;
- scope mismatch;
- uncertainty unbounded;
- material overclaim;
- absent adequacy boundary.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents M1 from collapsing into a generic
support-degradation label with no evidence-discipline boundary.

## Boundary

This pass is not an empirical validation of M1 and is not a source-complete
literature review.  It is a Lean-checked operational profile for the M1
candidate mechanism, with executable coverage checks and explicit blockers.

