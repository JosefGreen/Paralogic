# Reproducibility

## Environment

Local verification was run on Windows PowerShell from
`D:\WORK DRIVE\New folder\Paralogic Novel\Paralogic\Paralogic`.

## Lean Version

`Lean (version 4.19.0, x86_64-w64-windows-gnu, commit 6caaee842e94, Release)`

## Lake Build Command

Command: `lake build`

Result: pass. Output included `Build completed successfully.`

## Python Version

`Python 3.13.13`

## Test Commands

Command: `python -m pytest -q`

Result: pass. Output: `77 passed in 0.41s`.

After adding benchmark checkers, final pytest result: `79 passed`.

## Checker Commands

The following checker scripts from `.github/workflows/ci.yml` were run locally
and passed:

- `python python/finite_check.py`
- `python python/proof_check.py`
- `python python/propositional_proof_check.py`
- `python python/granularity_check.py`
- `python python/delta_check.py`
- `python python/repair_revision_check.py`
- `python python/evaluator_calibration_check.py`
- `python python/warrant_coverage_check.py`
- `python python/mechanism_coverage_check.py`
- `python python/metric_proxy_check.py`
- `python python/evidence_overclaim_check.py`
- `python python/formal_access_check.py`
- `python python/symbolic_substitution_check.py`
- `python python/repair_failure_check.py`
- `python python/translation_failure_check.py`
- `python python/veto_suppression_check.py`
- `python python/frame_drift_check.py`
- `python python/symbolic_overload_check.py`
- `python python/claim_discipline_check.py`
- `python python/usefulness_pilot_check.py`

## CI Workflow Summary

GitHub Actions builds Lean through `leanprover/lean-action@v1`, scans Lean
source for active hole markers, installs Python, runs pytest, and runs the
checker scripts listed above.

## Hole/Unsound Marker Scan

Command: `rg -n "\b(sorry|admit|unsafe|axiom)\b" src -g "*.lean"`

Result: pass. The command returned no matches.

## Expected Outputs

- Lean build succeeds.
- Pytest reports 77 passing tests.
- Final pytest reports 79 passing tests after benchmark checker tests are
  included.
- Checker scripts report pass statuses such as `MCC-pass`, `WCC-pass`,
  `M10C-pass`, `M11C-pass`, `CDC-pass`, and `UPC-pass`.
- `python python/claim_discipline_check.py` reports `CDC-pass` with zero
  warnings.
- Hole scan returns no matches.

## Known Limitations

Local Python version is 3.13.13; CI uses Python 3.12. Bounded Python checkers
are not global proofs. Lean checks selected fragments, not a complete system.

## Last Verified Commit

`e9bc70de301173a01907670219895de7cee92cfe`

## Usefulness Check

This document lets a reviewer reproduce the current benchmark checks without
guessing which commands matter.

## Claim Boundary

Passing these commands does not prove empirical validation, external review,
compliance, or complete mathematical coverage.
