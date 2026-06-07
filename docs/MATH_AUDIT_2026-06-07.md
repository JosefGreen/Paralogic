# Math Audit - 2026-06-07

Status: conservative audit against `Paralogic - Request for Agent Instructions.pdf`.

Verdict: the repository is not yet exhaustively developed. It is a clean
Lean-source starting point with useful anti-collapse witnesses, but it does not
complete the attached prompt's Bottleneck 1.

## Controlling Requirements From The PDF

The prompt requires a mathematics-first workflow:

1. Separate definitions, axioms, theorems, conjectures, countermodels,
   empirical hypotheses, normative bridges, heuristics, and deferred items.
2. Separate proof status from machine-check status and empirical status.
3. Never mark MC3-Lean unless Lean has actually run and accepted the code.
4. Protect every non-entailment with a countermodel.
5. Maintain non-collapse guards for every module.
6. Begin with Bottleneck 1: unified type signature and model semantics.

Bottleneck 1 specifically requires `Sigma_Paralogic`, sorts, function symbols,
predicate symbols, model class, interpretation, satisfaction relation, frame
semantics, context semantics, contradiction semantics, evaluator semantics,
ValidInsight semantics, ISF semantics, M8 semantics, NormativeBridge semantics,
and EmpiricalValidation semantics.

## Current Repository Coverage

Covered at first-kernel level:

1. Status labels exist in Lean.
2. Sort tags exist in Lean.
3. A finite one-object `World` exists.
4. `ISF`, `M8`, and `ValidInsight` are defined as Prop-valued conjunctions.
5. Selected definitional implications are encoded.
6. Selected non-entailments have named finite witnesses.
7. The docs explicitly block several reward-hacking moves.

Not yet covered to the PDF standard:

1. No complete many-sorted signature.
2. No named function-symbol or predicate-symbol arity table.
3. No model class `Mod(Sigma_Paralogic)` with carriers.
4. No interpretation function for symbols.
5. No variable assignments.
6. No formula syntax.
7. No genuine satisfaction relation for formulas.
8. No separation of syntactic entailment from semantic consequence.
9. No frame morphisms, context morphisms, projections, translations, or
   preservation profiles.
10. No formal contradiction semantics beyond a tag enum.
11. No evaluator criteria, soundness-relative-to-criteria, abstention,
    rejection, incompleteness, or meta-evaluator semantics.
12. No formal `Adeq` by domain.
13. No full M8 semantics.
14. No normative bridge schemas.
15. No repair calculus.
16. No empirical validation calculus.
17. No exhaustive finite model checker.
18. No custom proof checker.
19. No external literature novelty audit.
20. No empirical or external-review status beyond EMP0.

## Reward-Hacking Audit

Blocked by current code and docs:

1. `EvaluatorAccepts` does not imply `ValidInsight`.
2. `ValidInsight` does not imply empirical truth.
3. `ValidInsight` does not imply repair.
4. `ISF` does not imply M8.
5. M8 does not imply harm, illegality, or moral guilt.
6. Empirical validation does not imply governance legitimacy.

Still vulnerable:

1. Treating a one-object Boolean witness as full model theory.
2. Treating definitional projection theorems as deep proof.
3. Treating Lean source as Lean verification before a recorded build.
4. Treating `supportDegraded` as if it were a developed `Adeq` theory.
5. Treating M8's current conjunction as the full power-erasure mechanism.
6. Treating absence of bridge predicates as a complete normative boundary
   theory.

## Audit Conclusion

The current repository should be described as MC2 Lean-source scaffolding for a
finite kernel until build evidence is recorded. If `lake build` succeeds, only
the encoded finite-kernel statements become MC3-Lean. The broader Paralogic /
ISFT mathematics remains open.

The next mathematically honest step is not GitHub polish. It is Bottleneck 1:
replace the current `World` abstraction with a many-sorted model semantics and
then re-prove or re-witness the existing theorem ledger inside that richer
setting.
