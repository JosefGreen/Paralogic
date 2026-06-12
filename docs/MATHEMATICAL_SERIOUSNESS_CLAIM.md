# Mathematical Seriousness Claim

## One-Sentence Claim

"This is a Lean-checked formal research workbench for selected Paralogic/ISFT fragments, not a complete system."

## What This Repository Is

The repository contains Lean-checked selected definitions, implications,
countermodels, operational schemas, bounded executable checks, usefulness
pilots, and status ledgers for Paralogic/ISFT fragments. It is a formal
research workbench, not a finished theory.

## What This Repository Is Not

It is not a complete Paralogic system, not a complete ISFT system, not
empirical validation, not peer review, not legal or moral adjudication, and not
a compliance product.

## What Is Lean-Checked

Lean currently checks selected semantic kernels, proof-theory fragments,
model-theory infrastructure, finite witnesses, non-collapse countermodels,
operational warrant schemas, and mechanism-specific profiles for M1-M6 and
M9-M11.

## What Is Bounded Executable Checking

Python checkers rerun finite or syntactic checks over explicit bounded search
spaces or required source artifacts. These checks improve reproducibility, but
they are not global model-theoretic proofs.

## What Is Practical Usefulness Testing

The usefulness pilots test whether the workbench improves claim-boundary
discipline in realistic audit situations. Current pilot status: useful for
missing-warrant detection and safer-conclusion drafting, not proven generally
useful.

## What Is Documentation Or Protocol Only

Empirical protocols, review packets, roadmaps, and ledgers organize work. They
do not by themselves prove source backing, empirical support, legal status, or
real-world utility.

## What Is Not Empirically Validated

No empirical dataset, reliability statistic, construct-validation study, or
replication result currently validates Paralogic/ISFT as a real-world system.

## What Is Not Externally Reviewed

No external expert, peer reviewer, institutional reviewer, or standards body
has reviewed and approved the repository.

## What Is Safe To Cite

| Allowed claim | Evidence | Boundary | Link |
| --- | --- | --- | --- |
| Lean checks selected fragments. | `lake build` passes. | Selected fragments only. | `docs/REPRODUCIBILITY.md` |
| Some unsafe inferences are blocked in the formal scope. | Countermodels and tests. | Scope-bound, often finite. | `docs/WORKED_EXAMPLE_FORMAL_PIPELINE.md` |
| The workbench supports claim-boundary discipline. | Three usefulness pilots. | Not general utility proof. | `docs/REAL_WORLD_USEFULNESS_PILOTS.md` |

## What Is Unsafe To Cite

| Forbidden claim | Why forbidden | Required future evidence |
| --- | --- | --- |
| Paralogic is complete. | Many global gaps remain. | Completed theory, review, and proofs. |
| Paralogic is empirically validated. | No data/reliability/replication evidence. | Empirical study package. |
| ISFT proves harm, illegality, guilt, or wrongdoing. | Normative and legal bridges are guarded. | External standards, facts, and review. |
| The system satisfies a compliance regime. | No compliance mapping or audit. | Formal compliance assessment. |

## How To Verify

Run `lake build`, `python -m pytest -q`, the checker scripts listed in
`.github/workflows/ci.yml`, and the Lean hole-marker scan recorded in
`docs/REPRODUCIBILITY.md`.

## Current Maturity Labels

- Lean fragments: checked locally and in CI.
- Python checks: bounded or source-coverage checks.
- Usefulness pilots: initial synthetic pilots.
- Empirical status: protocol-only.
- External review: absent.

## Practical-Usefulness Status

The current practical value of Paralogic is claim-boundary discipline:
identifying missing warrants, blocking unsafe inferences, and producing safer
conclusions in selected audit scenarios.

## Next Work

Prioritize reviewer feedback, pilot refinement, warrant classification, and
simplification before adding more theory.

## Usefulness Check

This page helps a reader safely cite the repository without overstating it. It
does not prove any mathematical result.

## Claim Boundary

This document states public claim limits. It does not prove empirical truth,
harm, illegality, wrongdoing, moral guilt, institutional liability, or external
review.
