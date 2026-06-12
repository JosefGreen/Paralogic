# Model-Theory Status

## Executive Summary

The current model theory contains Lean-checked selected semantics,
preservation results, non-preservation countermodels, isomorphism results,
translation infrastructure, and finite witnesses. It is not yet a complete
model theory for Paralogic/ISFT.

## What The Model Theory Is For

It states what is preserved, what fails to be preserved, and what additional
conditions are needed before moving claims across models, frames, contexts, or
formula translations.

## Signature And Sort Layer

`CoreTypes.lean` defines typed sorts, predicate symbols, function symbols, and
signatures.

## Term Layer

`ModelSemantics.lean` defines typed terms and term evaluation.

## Formula Layer

The formula layer supports atoms, connectives, and quantifiers over the typed
signature.

## Satisfaction Layer

`SatisfiesFormula` defines semantic satisfaction under typed assignments.

## Assignment/Update Layer

Foundation lemmas describe assignment update, free-variable agreement, and
stability under non-free updates.

## Model Homomorphisms

Model homomorphisms preserve functions and positive predicate facts. They do
not preserve all formulas.

## Model Isomorphisms

Model isomorphisms include forward/backward homomorphisms and full formula
satisfaction equivalence.

## Formula Translations

Formula translations record translation of formulas and assignments with a
satisfaction-preservation obligation.

## Projection Laws

Projection-law infrastructure exists, but richer projection laws remain future
work.

## Preservation Theorems

The repository proves positive quantifier-free preservation under homomorphism
and full formula satisfaction equivalence under isomorphism.

## Non-Preservation Countermodels

Countermodels show homomorphisms do not preserve negation, implication, or
universal quantification without stronger hypotheses.

## Finite Models

The finite kernel includes one-object and many-sorted witnesses for selected
non-collapse claims.

## Nontrivial Finite Witnesses

Two-element witnesses separate `Uses` from `ISF` and `ISF` from `M8` in a more
informative finite setting than one-object examples.

## Many-Sorted Countermodels

Many-sorted countermodels support proof-theory and preservation boundaries.

## Relation To Executable Finite Checking

Python finite checks enumerate bounded valuation spaces and persist witnesses.
They do not replace global model-theoretic proof.

## Practical Usefulness

The model theory helps a reviewer see why some intuitive claim transfers are
invalid without extra hypotheses.

## Open Gaps

Open gaps include richer frame histories, global finite-model search,
source-backed mechanism semantics, full projection laws, and external review.

## Usefulness Check

This page helps reviewers locate preservation and non-preservation boundaries
without reading every Lean file first.

## Claim Boundary

This page does not claim a complete model theory, empirical validation,
external review, or real-world adjudication.
