# Propositional Proof Check Report - 2026-06-08

Status: PPC-bounded pass.

This checker mirrors the propositional fragment strengthened in
`src/Paralogic/ProofTheory.lean`.

## Scope

The Lean calculus now includes:

- premise use
- truth introduction
- falsity elimination
- conjunction introduction and elimination
- disjunction introduction and elimination
- implication introduction and elimination
- scoped universal current-value elimination in Lean
- scoped existential current-value introduction in Lean
- universal introduction under semantic premise-stability in Lean
- direct semantic universal-introduction theorems under stability and
  no-free-variable freshness in Lean
- syntactic no-free-variable freshness bridge to premise stability in Lean
- a Lean countermodel blocking unrestricted universal introduction from a
  premise with the generalized variable free

The executable checker truth-table checks seven propositional targets:

- conjunction-left elimination
- modus ponens
- implication introduction
- falsity elimination
- disjunction elimination
- rejection of affirming the consequent
- rejection of disjunctive affirmation

## Main Bounded Result

All seven targets passed.  The positive targets are semantically valid under
all Boolean valuations of their atoms, and the two negative controls are not
valid entailments.

## Anti-Overclaim Guard

This is not a completeness theorem for the many-sorted first-order language.
The executable checker covers a small propositional truth-table fragment.  Lean
proves semantic soundness for the encoded `Derives` calculus against
`SatisfiesFormula`; only the scoped current-value quantified rules and
semantic-stability universal introduction are encoded, with a quantifier-free
freshness bridge retained as a bounded subcase of the full no-free-variable
stability theorem.  The semantic-consequence layer has matching guarded
universal-introduction theorems.  Lean also contains a countermodel showing
that unrestricted universal introduction is not sound when a premise depends on
the generalized variable.  Full quantified proof theory with alpha-equivalence,
eigenvariable discipline, and completeness remain open.

## Artifacts

- `src/Paralogic/ProofTheory.lean`
- `python/propositional_proof_check.py`
- `docs/propositional_proof_checks/coverage.json`
- `docs/propositional_proof_checks/PPC-CONJ-LEFT.json`
- `docs/propositional_proof_checks/PPC-MODUS-PONENS.json`
- `docs/propositional_proof_checks/PPC-IMPL-INTRO.json`
- `docs/propositional_proof_checks/PPC-FALSITY-ELIM.json`
- `docs/propositional_proof_checks/PPC-DISJ-ELIM.json`
- `docs/propositional_proof_checks/PPC-REJECT-AFFIRMING-CONSEQUENT.json`
- `docs/propositional_proof_checks/PPC-REJECT-DISJUNCTIVE-AFFIRMATION.json`
