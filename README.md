# Paralogic

Paralogic is a Lean-first research program for formalizing frame-relative
contradiction, evaluator-gated insight, non-collapse reasoning, and ISFT
(Institutional Symbolic Failure Theory).

This repository has been rebuilt from scratch as a mathematical workbench.
The current target is rigor, not rhetoric: every major claim must become a
typed definition, theorem, countermodel, proof obligation, or validation gap.

## What Is Encoded Now

The current Lean kernel encodes a finite one-object semantic fragment:

- `ISF -> Uses`
- `ISF -> Claims`
- `ISF -> SupportDegraded`
- `ISF -> TreatsAsAdequate`
- `M8 -> ISF`
- `ValidInsight -> EvaluatorAccepts`
- countermodels for `Uses not-> ISF`
- countermodels for `ISF not-> M8`
- countermodels for `M8 not-> Harm / Illegality / MoralGuilt`
- countermodels for `EvaluatorAccepts not-> ValidInsight`
- countermodels for `ValidInsight not-> EmpiricalTruth / Repair`
- countermodels for `EmpiricalValidation not-> GovernanceLegitimacy`

Those are Lean theorem statements over a deliberately small kernel. They are
not empirical validation and they are not a complete formalization of all
Paralogic. They should be labeled MC3-Lean only after `lake build` has
actually run and accepted the repository in a trusted environment.

## Build

```bash
lake build
```

The project intentionally avoids Mathlib for now so the foundational kernel is
small, auditable, and easy to build.

## Repository Map

- `src/Paralogic/Status.lean` - status labels and anti-overclaim machinery.
- `src/Paralogic/CoreTypes.lean` - typed vocabulary and signature skeleton.
- `src/Paralogic/Semantics.lean` - finite semantic world.
- `src/Paralogic/ISFT.lean` - ISF and M8 definitions.
- `src/Paralogic/Insight.lean` - ValidInsight definition.
- `src/Paralogic/Countermodels.lean` - finite witness models.
- `src/Paralogic/Theorems.lean` - theorem ledger encoded in Lean.
- `src/Paralogic/TestSuite.lean` - Lean examples that act as regression tests.
- `docs/` - formal specification, theorem ledger, gap ledger, audit, and roadmap.

## Non-Negotiable Claim Discipline

Do not claim:

- Paralogic is complete.
- Paralogic is empirically validated.
- ISFT proves wrongdoing, illegality, harm, or guilt.
- M8 proves discrimination, coercion, harm, illegality, moral guilt, or repair
  obligation.
- ValidInsight proves empirical truth, moral truth, or repair.
- Evaluator acceptance proves truth.

Permitted current claim before a recorded successful build:

The repository contains Lean source for a finite kernel with typed definitions,
core implications, and explicit countermodels for selected non-entailments.

Permitted current claim after a recorded successful `lake build`:

The repository contains a Lean-checked finite kernel for selected definitions,
implications, and non-entailment witnesses.

## Next Mathematical Bottlenecks

1. Replace the one-object world with a many-sorted first-order model class.
2. Add typed frame/context morphisms and preservation profiles.
3. Add evaluator criteria, soundness-relative-to-criteria, and incompleteness.
4. Expand M8 with typed power conditions and bridge predicates.
5. Build a normative bridge library without smuggling moral/legal conclusions.
6. Add finite model enumeration and countermodel search inside Lean or an
   audited companion checker.
7. Develop `Adeq` by domain with empirical coding protocols.
8. Formalize delta outcome classification.
9. Formalize repair calculus.
10. Add empirical validation artifacts only after operationalization.
