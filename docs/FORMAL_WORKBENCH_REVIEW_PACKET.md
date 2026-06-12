# Formal Workbench Review Packet

## Reviewer Summary

Paralogic is currently a Lean-checked formal research workbench for selected
fragments, not a complete mathematical system. Review should focus on claim
boundaries, theorem depth, warrant status, and usefulness pilots before new
theory is added.

## Repository Entry Points

- `README.md`
- `docs/CURRENT_STATUS.md`
- `docs/MATHEMATICAL_SERIOUSNESS_CLAIM.md`
- `docs/REPRODUCIBILITY.md`

## Minimal Review Path

1. Read `docs/MATHEMATICAL_SERIOUSNESS_CLAIM.md`.
2. Read `docs/WORKED_EXAMPLE_FORMAL_PIPELINE.md`.
3. Run `lake build` and `python -m pytest -q`.
4. Inspect `docs/REAL_WORLD_USEFULNESS_PILOTS.md`.
5. Check `docs/THEOREM_DEPTH_LEDGER.md` and `docs/WARRANT_LEDGER.md`.

## Deep Review Path

1. Inspect proof and model status pages.
2. Review `src/Paralogic/ProofTheory.lean` and `src/Paralogic/FrameContext.lean`.
3. Review non-collapse countermodels.
4. Review warrant discharge and mechanism profiles.
5. Compare Python checker scopes to Lean artifacts.

## What To Inspect First

Inspect the claims that would be easiest to overstate: evaluator acceptance,
ValidInsight, M8, operational warrant coverage, mechanism profiles, and
bounded Python checks.

## What Not To Infer

Do not infer completeness, empirical validation, external review, wrongdoing,
harm, illegality, guilt, discrimination, compliance, or commercial readiness.

## Practical Usefulness Pilots

See `docs/REAL_WORLD_USEFULNESS_PILOTS.md`.

## Current Proof-Theory Status

See `docs/PROOF_THEORY_STATUS.md`.

## Current Model-Theory Status

See `docs/MODEL_THEORY_STATUS.md`.

## Theorem-Depth Ledger

See `docs/THEOREM_DEPTH_LEDGER.md` and
`docs/ledgers/theorem_depth_ledger.csv`.

## Warrant Ledger

See `docs/WARRANT_LEDGER.md` and `docs/ledgers/warrant_ledger.csv`.

## Worked Example

See `docs/WORKED_EXAMPLE_FORMAL_PIPELINE.md`.

## Reviewer Questions

1. Are theorem-depth classifications accurate?
2. Are any D4/D5 items overclassified?
3. Are supplied warrants being treated as derived?
4. Are the usefulness pilots genuinely useful?
5. Does the audit template improve ordinary prose?
6. Are the proof-theory caveats sufficient?
7. Are the model-theory caveats sufficient?
8. Are public-facing statements still overreaching?
9. Which parts should be simplified?
10. Which parts deserve external review first?

## How To Report Issues

Open a GitHub issue with the file, line, claim, risk, and suggested safer
wording or proof obligation.

## Usefulness Check

This packet helps reviewers inspect the project without reading every file
first.

## Claim Boundary

This packet is a review guide. It is not peer review, external approval,
empirical validation, or proof of usefulness.
