# Proof Check Report - 2026-06-07

Status: PYC-pass.

`python/proof_check.py` implements a small checker for Horn-like definitional
implications.  It validates proof traces by premise introduction and named
rule application, and it rejects unsupported conclusions or missing premises.

## Outputs

- Coverage file: `docs/proof_checks/coverage.json`
- Individual trace files: `docs/proof_checks/PYC-*.json`

## Checked Traces

| ID | Expected | Result |
| --- | --- | --- |
| PYC-ISF-USES | accept | accepted |
| PYC-M8-ISF | accept | accepted |
| PYC-M8-USES | accept | accepted |
| PYC-VALID-INSIGHT-EVAL | accept | accepted |
| PYC-REJECT-EVAL-TO-VALID-INSIGHT | reject | rejected |
| PYC-REJECT-MISSING-M8-PREMISE | reject | rejected |

## Scope Guard

PYC status is not Lean verification, empirical validation, or a replacement
for external review.  It is an independent executable check for the small
Horn-like rule set encoded in the script.
