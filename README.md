# Paralogic

"This is a Lean-checked formal research workbench for selected Paralogic/ISFT fragments, not a complete system."

Paralogic is a Lean-first research program for formalizing frame-relative
contradiction, evaluator-gated insight, non-collapse reasoning, and ISFT
(Institutional Symbolic Failure Theory).

This repository has been rebuilt from scratch as a mathematical workbench.
The current public benchmark is practical mathematical seriousness: selected
Lean-checked fragments, reproducible checks, usefulness pilots, and explicit
claim boundaries.

Current status: incomplete.  See `docs/CURRENT_STATUS.md` and
`docs/FULL_SYSTEM_AUDIT_2026-06-08.md`.

Safe expanded claim:

The repository contains Lean-checked selected definitions, implications,
countermodels, operational schemas, bounded executable checks, usefulness
pilots, and status ledgers for Paralogic/ISFT fragments. It is a formal
research workbench, not a complete mathematical system, not empirical
validation, and not an external-review substitute.

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

## Verification

```bash
lake build
python -m pytest -q
```

For the full local verification list, see `docs/REPRODUCIBILITY.md`.

## Practical Mathematical-Seriousness Benchmark

Benchmark entry points:

- `docs/MATHEMATICAL_SERIOUSNESS_CLAIM.md`
- `docs/ANTI_REWARD_HACKING_AUDIT.md`
- `docs/SIMPLIFICATION_LOG.md`
- `docs/REAL_WORLD_USEFULNESS_PILOTS.md`
- `docs/PARALOGIC_CLAIM_AUDIT_TEMPLATE.md`
- `docs/THEOREM_DEPTH_LEDGER.md`
- `docs/ledgers/theorem_depth_ledger.csv`
- `docs/WARRANT_LEDGER.md`
- `docs/ledgers/warrant_ledger.csv`
- `docs/PROOF_THEORY_STATUS.md`
- `docs/MODEL_THEORY_STATUS.md`
- `docs/WORKED_EXAMPLE_FORMAL_PIPELINE.md`
- `docs/REPRODUCIBILITY.md`
- `docs/CLAIM_DISCIPLINE_AUDIT.md`
- `docs/FORMAL_WORKBENCH_REVIEW_PACKET.md`

Complete for the current benchmark: public claim boundary, reproducibility
record, three usefulness pilots, practical audit template, scoped theorem-depth
ledger, scoped warrant ledger, proof/model status pages, worked example, review
packet, and claim-discipline audit.

Still globally incomplete: full Paralogic/ISFT theory, source-backed semantics
for all mechanisms, proof-theory completeness, global finite-model search,
empirical validation, and external review.

## Repository Map

- `src/Paralogic/Status.lean` - status labels and anti-overclaim machinery.
- `src/Paralogic/CoreTypes.lean` - typed vocabulary and signature skeleton.
- `src/Paralogic/ModelSemantics.lean` - many-sorted model semantics.
- `src/Paralogic/FrameContext.lean` - model/frame/context morphisms.
- `src/Paralogic/NormativeBridge.lean` - explicit normative bridge schemas.
- `src/Paralogic/Repair.lean` - staged repair calculus and bridge independence.
- `src/Paralogic/EmpiricalValidation.lean` - empirical validation protocols.
- `src/Paralogic/FiniteModels.lean` - finite Boolean valuation models.
- `src/Paralogic/Adequacy.lean` - domain-relative adequacy profiles.
- `src/Paralogic/Evaluator.lean` - evaluator criteria and relative soundness.
- `src/Paralogic/M8Power.lean` - M8 power-erasure condition schemas.
- `src/Paralogic/ISFTMechanisms.lean` - M1-M12 mechanism scaffold.
- `src/Paralogic/Semantics.lean` - finite semantic world.
- `src/Paralogic/ISFT.lean` - ISF and M8 definitions.
- `src/Paralogic/Insight.lean` - ValidInsight definition.
- `src/Paralogic/Countermodels.lean` - finite witness models.
- `src/Paralogic/Theorems.lean` - theorem ledger encoded in Lean.
- `src/Paralogic/TestSuite.lean` - Lean examples that act as regression tests.
- `python/finite_check.py` - bounded executable finite checker.
- `python/proof_check.py` - scoped Horn-like proof checker.
- `docs/finite_checks/` - EFC-bounded coverage and witness artifacts.
- `docs/proof_checks/` - PYC proof traces and rejection artifacts.
- `docs/empirical/` - EMP0 empirical protocol artifacts.
- `docs/academic/` - internal related-work, reducibility, and review packet.
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
- The repository is peer reviewed.
- The repository is a commercial assurance or compliance product.

Permitted current claim before a recorded successful build:

The repository contains Lean source for a finite kernel with typed definitions,
core implications, and explicit countermodels for selected non-entailments.

Permitted current claim after a recorded successful `lake build`:

The repository contains Lean-checked finite and many-sorted kernel fragments
for selected definitions, implications, non-entailment witnesses, and
condition-gated semantic schemas.

Practical-usefulness claim:

The current practical value of Paralogic is claim-boundary discipline:
identifying missing warrants, blocking unsafe inferences, and producing safer
conclusions in selected audit scenarios.

## CALM / Paper Armies Workstream

The repository now also contains an early internal workstream for CALM
(Capability Assurance and Learning Mobility) and the book project Paper Armies.
These artifacts use Paralogic-style claim-boundary discipline as backend
method; they do not claim that Paralogic proves CALM or validates any defense
case.

- `docs/calm/PROJECT_CHARTER.md` - Phase 0 identity, posture, guardrails, and
  completion criteria.
- `docs/calm/COMPLETION_PIPELINE.md` - full CALM / Paper Armies completion
  pipeline.
- `docs/calm/PAPER_ARMIES_ARCHITECTURE.md` - controlled book architecture.
- `docs/calm/SOURCE_CASE_DOSSIER_TEMPLATE.md` - source and case packet schema.
- `docs/calm/source_dossier/README.md` - generated source dossier from the
  attached Paper Armies / CALM source-map workbook.
- `docs/calm/CALM_FORMAL_SPEC.md` - map from the initial Lean CALM guard core
  to doctrine/toolkit use.
- `src/Paralogic/CALM.lean` - selected checked non-collapse guards for claim
  travel, learning travel, and Paper CALM reflexivity.

## Next Mathematical Bottlenecks

1. Prove substitution and satisfaction lemmas for the many-sorted formula layer.
2. Strengthen frame/context morphisms with projection and translation laws.
3. Obtain external expert review.
4. Run pilot empirical work only after protocol review.
5. Develop validation claims only after reliability, validity, and replication
   evidence exists.
