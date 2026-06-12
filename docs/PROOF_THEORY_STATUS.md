# Proof-Theory Status

## Executive Summary

The current proof theory contains a Lean-checked soundness theorem for a scoped
derivability calculus. It is not yet a complete natural-deduction system for
the full quantified formula language.

## What The Proof Theory Is For

It tests which formula transformations are safe inside the current formal
language and blocks common invalid shortcuts, especially around implication,
disjunction, falsity, and quantifier freshness.

## Formal Objects Covered

The main objects are formulas, premises, assignments, semantic satisfaction,
semantic entailment, and derivability rules.

## Formula Language Summary

The language includes truth, falsity, atoms, conjunction, disjunction,
implication, negation, universal quantification, and existential
quantification.

## Satisfaction Relation Summary

`SatisfiesFormula` evaluates formulas under a typed assignment in a
many-sorted model.

## Derivability Relation Summary

`Derives` encodes a scoped derivability calculus with selected introduction
and elimination rules.

## Rules Currently Encoded

Current rules include premise use, truth introduction, falsity elimination,
conjunction rules, disjunction rules, implication rules, scoped current-value
quantifier rules, and guarded universal introduction.

## Soundness Theorem Currently Proved

Selected derivability examples and rule families are proved sound against
semantic entailment in Lean.

## Freshness/Stable Conditions Currently Proved

The repository proves assignment-agreement and no-free-variable stability
lemmas sufficient for guarded universal introduction.

## Quantifier Rules Currently Covered

Universal current-value elimination, existential current-value introduction,
and universal introduction under premise stability or freshness are covered.

## Known Countermodels Blocking Unsafe Rules

The many-sorted countermodels block unrestricted universal introduction where a
premise contains the quantified variable free.

## What Remains Open

Full natural deduction, alpha-equivalence, substitution theory for all cases,
complete quantified proof theory, and completeness results remain open.

## What Fragment Completeness Could Mean

A future fragment-completeness claim would need a declared fragment, proof
rules, semantic class, and proof that every semantically valid consequence in
that fragment is derivable.

## Relation To Python Proof Checkers

`python/proof_check.py` and `python/propositional_proof_check.py` provide
bounded executable checks and regression traces. They do not replace Lean
proofs.

## Practical Usefulness

The proof theory helps block invalid proof steps and supports a public
claim-boundary example around universal introduction.

## Usefulness Check

This page tells a reviewer what proof-theory claims are safe to make and where
the boundaries are.

## Claim Boundary

This page does not claim proof-theory completeness, a full natural-deduction
system, empirical validation, or external review.
