# Formal Specification v0.2

Status: Lean-source finite kernel, not complete Paralogic.

Machine-check status: MC2 until `lake build` is actually executed and recorded
as successful. Any successful build may promote the checked files to MC3-Lean
for exactly those encoded statements, not for the larger Paralogic / ISFT
program.

## Objective

Define the smallest rigorous Paralogic / ISFT core that can be checked in
Lean immediately, then grow it conservatively.

## Current Signature

The current signature is represented in `CoreTypes.lean`.

Sort tags:

- Institution
- SymbolicOutput
- Claim
- EvidenceSet
- Context
- Time
- Frame
- Evaluator
- CandidateInsight
- PowerCondition
- AffectedGroup
- NormativeBridge
- EmpiricalValidationObject

Core semantic predicates live as fields of `World`.

## Defined Predicates

`ISF w` iff:

- `w.uses`
- `w.claims`
- `w.supportDegraded`
- `w.treatsAsAdequate`

`M8 w` iff:

- `w.uses`
- `w.claims`
- `w.powerRelevant`
- `w.powerValidityDependence`
- `w.powerOmitted`
- `w.supportDegraded`
- `w.treatsAsAdequate`

`ValidInsight w` iff:

- `w.candidateInsight`
- `w.evaluatorAccepts`
- `w.licensedTransition`
- `w.nonTrivialTransformation`
- `w.contradictionAddressed`
- `w.noHigherOrderDefeater`
- `w.generativityMinimal`
- `w.directionalNonEquivalence`

## Model Semantics

The current model class is a one-object finite abstraction. A `World` assigns a
truth value to each primitive predicate. Defined predicates are Lean
structures whose fields require the relevant primitive propositions.

This is intentionally weaker than a full many-sorted first-order semantics.
The next model layer must define carriers, typed functions, predicate
interpretations, assignments, and a satisfaction relation.

## Current Theorem Families

Positive entailments:

- `ISF -> Uses`
- `ISF -> Claims`
- `ISF -> SupportDegraded`
- `ISF -> TreatsAsAdequate`
- `M8 -> ISF`
- `ValidInsight -> EvaluatorAccepts`

Non-entailments by countermodel:

- `Uses not-> ISF`
- `Claims not-> ISF`
- `SupportDegraded not-> ISF`
- `Uses + Claims + SupportDegraded not-> ISF`
- `ISF not-> M8`
- `M8 not-> Harm`
- `M8 not-> Illegality`
- `M8 not-> MoralGuilt`
- `EvaluatorAccepts not-> ValidInsight`
- `ValidInsight not-> EmpiricalTruth`
- `ValidInsight not-> Repair`
- `DeltaResolution not-> EmpiricalTruth`
- `EmpiricalValidation not-> GovernanceLegitimacy`

## Non-Collapse Guard

The kernel explicitly separates:

- formal diagnosis from moral guilt;
- power erasure from discrimination, coercion, and harm;
- evaluator acceptance from truth;
- valid insight from empirical truth and repair;
- empirical validation from governance legitimacy.

## Verification Status

Lean theorem status: MC2 in this ledger until `lake build` succeeds and the
build result is recorded.

Empirical status: EMP0.

External review status: none recorded.
