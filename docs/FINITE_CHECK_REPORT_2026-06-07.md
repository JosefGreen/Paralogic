# Finite Check Report - 2026-06-07

Status: EFC-bounded.

This report records executable bounded finite checks produced by
`python/finite_check.py`.  The checker enumerates every Boolean valuation over
the atom set relevant to each target.  It does not claim a global exhaustive
search over the complete many-sorted signature.

## Outputs

- Coverage file: `docs/finite_checks/coverage.json`
- Combined witness file: `docs/finite_checks/witnesses.json`
- Individual witness files: `docs/finite_checks/EFC-*.json`

## Coverage Summary

| ID | Result | Valuations |
| --- | --- | --- |
| EFC-ISF-USES-NOT-ISF | counterexample found as expected | 16 |
| EFC-ISF-IMPLIES-USES | no counterexample found as expected | 16 |
| EFC-M8-ISF-NOT-M8 | counterexample found as expected | 128 |
| EFC-M8-IMPLIES-ISF | no counterexample found as expected | 128 |
| EFC-M8-NOT-HARM | counterexample found as expected | 256 |
| EFC-EVAL-NOT-VALID-INSIGHT | counterexample found as expected | 256 |
| EFC-VALID-INSIGHT-IMPLIES-EVAL | no counterexample found as expected | 256 |
| EFC-VALID-INSIGHT-NOT-EMPIRICAL-TRUTH | counterexample found as expected | 512 |
| EFC-VALID-INSIGHT-NOT-REPAIR | counterexample found as expected | 512 |
| EFC-EMPIRICAL-VALIDATION-NOT-GOVERNANCE | counterexample found as expected | 4 |

## Reward-Hacking Guard

These files are executable evidence for bounded finite targets only.  They do
not establish empirical validation, moral/legal conclusions, external review,
or global completeness of Paralogic.
