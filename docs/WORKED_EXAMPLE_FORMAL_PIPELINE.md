# Worked Example: Evaluator Acceptance Does Not Prove Truth

## Plain-Language Real-World Version

An AI evaluation report says a system was accepted by an evaluator panel, then
concludes that the system's output is true in the real world.

## Informal Paralogic Idea

Evaluator acceptance and empirical truth are different claim types. Acceptance
can be useful evidence, but it does not by itself supply the empirical warrant.

## Typed Objects

The finite semantic kernel uses a `World` with fields including
`evaluatorAccepts`, `candidateInsight`, and `empiricalTruth`.

## Semantic Predicate

`ValidInsight` includes evaluator acceptance and other internal fields.
`empiricalTruth` is a separate primitive field in the finite world.

## Theorem Or Countermodel

The repository contains `ValidInsight_does_not_imply_empiricalTruth`, a
Lean-checked countermodel showing that `ValidInsight` can hold while
`empiricalTruth` does not hold in the finite kernel.

## Checker/Test Relation

`python/finite_check.py` includes the corresponding target
`EFC-VALID-INSIGHT-NOT-EMPIRICAL-TRUTH`, and the persisted witness is stored in
`docs/finite_checks/`.

## What Ordinary Prose Would Say

"An evaluator accepted it" is not the same as "it is true."

## What The Formal Workbench Adds

The formal workbench turns that prose warning into a repeatable
non-entailment check. It shows the exact inference that fails inside the
formal fragment and keeps the safer conclusion separate from stronger claims.

## What The Example Proves

It proves a scoped non-collapse result: within the current finite kernel,
`ValidInsight` does not entail `empiricalTruth`.

## What It Does Not Prove

It does not prove that any real evaluator is wrong, that any real output is
false, or that ValidInsight is generally unreliable.

## Safer Conclusion

The system has evaluator acceptance or a valid-insight status in the formal
fragment. Empirical truth remains a separate claim requiring empirical
evidence.

## How To Verify

Run `lake build` and `python python/finite_check.py`.

## How To Cite Safely

Safe: "The repository includes a Lean-checked finite countermodel showing that
ValidInsight does not entail empirical truth in the current formal kernel."

Unsafe: "Paralogic proves evaluator-accepted systems are false."

## Required Final Wording

"This example demonstrates formal non-collapse or guarded projection inside
the current Paralogic workbench. It does not establish empirical truth, harm,
illegality, wrongdoing, moral guilt, or institutional liability."

## Usefulness Check

This example helps a public reader understand how the repository blocks a
common false inference.

## Claim Boundary

This worked example is scoped to the current formal workbench. It does not
prove empirical truth, harm, illegality, wrongdoing, moral guilt, or
institutional liability.
