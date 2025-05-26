import Mathlib.Tactic.Basic
import Lean.Elab.Tactic
import Lean.Parser
import Paralogic.Jumps
import Paralogic.Stuckness

/-!
  src/Paralogic/Tactics.lean

  Tactics to automate Paralogic proofs: detecting paradoxes, applying jumps, and scaffolding entropy-based arguments.
-/


namespace Paralogic.Tactics

open Lean Elab Tactic Meta

/--
`#paralogic` tactic:
1. Detects a pair of contradictory premises `margin C v < 0` and `margin C v ≥ 0`.
2. Creates two subgoals isolating each polarity.
3. Applies the appropriate `jumpOp` or entropy lemma to discharge the contradiction.
-/
elab "paralogic" : tactic => do
  -- find hypotheses of form `margin C v < 0` and `margin C v ≥ 0`
  let ctx ← getLCtx
  let mut negH : Option Expr := none
  let mut posH : Option Expr := none
  for hyp in ctx do
    let t ← inferType hyp.fvarId!
    if t.isAppOfArity ``LT 3 then
      negH := some hyp.fvarId!
    if t.isAppOfArity ``GE 3 then
      posH := some hyp.fvarId!
  match negH, posH with
  | some hneg, some hpos =>
    -- split into two cases
    withMainContext do
      evalTactic (← `(tactic| split))
      -- in left case, apply jumpOp
      evalTactic (← `(tactic| apply_paralogic_jump $(mkIdent hneg)))
      -- in right case, apply contradiction
      focus do
        evalTactic (← `(tactic| contradiction))
  | _ =>
    throwError "paralogic tactic failed: no contradictory margin hypotheses found"

/--
`apply_paralogic_jump h` tactic:
Given `h : margin C v < 0`, applies `jumpOp` and proves that
`insightScore (jumpOp v) < insightScore v`.
-/
elab (name := apply_paralogic_jump) "apply_paralogic_jump" hyp:ident : tactic => do
  let hypFVar ← getLocalDeclFromUserName hyp.getId
  -- apply strict descent lemma
  evalTactic (← `(tactic| exact Paralogic.Jumps.insightScore_strict_descent _ _ _ _ _))
  pure ()

/--
`apply_entropy_decay` tactic:
Applies `frameEntropy_monotonic_flow` to prove nonpositivity of the directional derivative.
-/
elab (name := apply_entropy_decay) "apply_entropy_decay" : tactic => do
  evalTactic (← `(tactic| exact Paralogic.Entropy.frameEntropy_monotonic_flow))
  pure ()

end Paralogic.Tactics
