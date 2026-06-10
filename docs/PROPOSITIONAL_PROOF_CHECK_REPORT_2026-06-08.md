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
`SatisfiesFormula`; quantified introduction/elimination and completeness
remain open.

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
