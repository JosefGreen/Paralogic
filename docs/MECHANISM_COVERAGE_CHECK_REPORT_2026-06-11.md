# Mechanism Coverage Check Report - 2026-06-11

Status: `MCC-pass`.

This report records the executable coverage check for the candidate M1-M12
mechanism layer.  The check is intentionally narrow: it confirms that the
current formal mechanism scaffold is complete as a candidate surface, while
leaving source-backed and empirical validation claims outside this result.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/ISFTMechanisms.lean`
  - `src/Paralogic/MechanismSynthesis.lean`
- Executable checker:
  - `python/mechanism_coverage_check.py`
- Persisted outputs:
  - `docs/mechanism_coverage_checks/coverage.json`
  - `docs/mechanism_coverage_checks/mechanisms.json`

## Coverage Result

The checker confirms:

- exactly 12 declared `ISFTMechanism` constructors;
- exactly 12 listed mechanisms in `allISFTMechanisms`;
- no duplicate declared or listed mechanisms;
- exhaustive case coverage for:
  - `mechanismIndex`;
  - `mechanismName`;
  - `mechanismLens`;
  - `mechanismFailureAxis`;
- required candidate fields in `unitCandidateDefinition`;
- required Lean coverage theorems, including
  `candidate_mechanism_coverage_complete`.

## Formal Result

The Lean core now proves:

- every mechanism is listed in `allISFTMechanisms`;
- the list has length 12 and has no duplicates;
- every mechanism index is positive and bounded by 12;
- every unit candidate preserves its mechanism label, assigned lens, and
  failure axis;
- every unit candidate satisfies the candidate definition and derived
  mechanism profile;
- no unit candidate mechanism is promoted to source-backed or empirically
  validated status;
- `CandidateMechanismCoverageComplete`.

## Anti-Overclaim Boundary

This check does not prove that M1-M12 are externally validated mechanisms.  It
proves that the current candidate-synthesized mechanism scaffold is total over
the twelve labels, internally mapped, formally regression-tested, and blocked
from being mistaken for source-backed or empirically validated semantics.

