# Evaluator Calibration Check Report - 2026-06-08

Status: ECC-bounded pass.

This checker mirrors the finite evaluator scoring and aggregation fragment in
`src/Paralogic/EvaluatorCalibration.lean`.

## Scope

- score levels checked: `low`, `medium`, `high`
- score decisions checked:
  - `low` -> `rejects`
  - `medium` -> `abstains`
  - `high` -> `accepts`
- three-evaluator score triples checked: 27
- majority rule: two or more accepting scores yield `accepts`; two or more
  rejecting scores yield `rejects`; all remaining triples yield `abstains`

## Main Bounded Result

The exhaustive 27-triple sweep found zero majority-rule failures.

The checker also verifies Lean-named witnesses for high-score acceptance,
low/medium non-acceptance, score disagreement, and representative majority
accept/reject/abstain triples.

## Anti-Overclaim Guard

This is a bounded finite decision-procedure check.  It does not provide
empirical calibration, inter-rater reliability statistics, validity evidence,
or an externally justified scoring rubric.  It only supplies a checked local
operational layer so evaluator acceptance is no longer represented solely by
warrant fields and record projections.

## Artifacts

- `src/Paralogic/EvaluatorCalibration.lean`
- `python/evaluator_calibration_check.py`
- `docs/evaluator_calibration_checks/triples.json`
- `docs/evaluator_calibration_checks/summary.json`
- `docs/evaluator_calibration_checks/lean_named_witnesses.json`
- `docs/evaluator_calibration_checks/coverage.json`
