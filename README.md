# Paralogic

Paralogic is a research prototype for formalizing frame-relative
contradiction, recursive transformation, evaluator-gated insight, failure
classification, and ISFT (Institutional Symbolic Failure Theory).

The current repository goal is conservative: make the formal core explicit,
testable, and honest about proof status. It does not claim that Paralogic is
complete, empirically validated, Lean-verified, morally authoritative, or a
new school of mathematics.

## Current Status

- Text-level formalization: in progress.
- Python executable finite checks: available for the small ISFT/ValidInsight
  definitional fragment.
- Lean sources: candidate/scaffold layer only until `lake build` succeeds in a
  configured Lean toolchain.
- Machine-check status: no MC3-Lean claim is made by this repository.
- Empirical status: no empirical validation is claimed.

See `docs/STATUS.md` for the detailed status discipline.

## Repository Map

- `python/paralogic_core.py` - earlier numerical prototype helpers.
- `python/paralogic_isft_core.py` - executable finite checker for the core
  ISFT/M8/ValidInsight fragment.
- `python/run_core_checks.py` - standard-library runner for the finite checks.
- `python/tests/` - pytest tests.
- `src/Paralogic/` - Lean candidate sources.
- `docs/` - formal baseline, theorem ledger, gap ledger, and dependency graph.

## Quick Checks

Run the finite core checker without installing test tooling:

```bash
python python/run_core_checks.py
```

Run the Python tests after installing requirements:

```bash
python -m pip install -r python/requirements.txt
python -m pytest python/tests -q
```

Lean checking is intentionally not part of the required local path until the
toolchain and imports are stable:

```bash
lake build
```

Only treat Lean results as MC3-Lean after a trusted Lean toolchain actually
accepts the files.

## Core Finite Fragment

The executable checker currently covers:

- `ISF -> Uses`
- `ISF -> Claims`
- `ISF -> SupportDegraded`
- `ISF -> TreatsAsAdequate`
- `M8 -> ISF`
- non-entailment guards such as `Uses not-> ISF`, `CandidateInsight not->
  ValidInsight`, `EvaluatorAccepts not-> ValidInsight`, and `M8 not-> Harm`.

These are finite truth-table checks and custom Horn-definition checks only.
They support EFC/EFE/PYC labels for the encoded fragment, not whole-system
proofs.

## Non-Collapse Rules

This repository explicitly blocks the following overclaims:

- Contradiction does not imply insight.
- Evaluator acceptance does not imply truth.
- ValidInsight does not imply empirical truth, moral truth, or repair.
- ISF does not imply guilt, illegality, harm, or repair obligation.
- M8 does not imply discrimination, coercion, harm, illegality, moral guilt, or
  repair obligation.
- Audit traces do not imply accountability.
- Empirical validation does not imply governance legitimacy.
- Proof-ready does not mean proof-checked.

## Development Priority

The next mathematical bottleneck is Bottleneck 1: unified type signature and
model semantics for the Paralogic / ISFT core. The current baseline is in
`docs/BOTTLENECK_1_SIGNATURE_AND_MODEL_SEMANTICS.md`.
