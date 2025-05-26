import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Deriv

/-!
  src/Paralogic/Oscillator.lean

  A deterministic linear oscillator: exponential decay on ℝⁿ.
-/


namespace Paralogic.Oscillator

open Real

variable {n : Type*} [Fintype n]

/--
An `Oscillator` is a system on ℝⁿ with uniform decay rate `λ > 0`:
the ODE is `ẋ(t) = -λ • x(t)`.
-/
structure Oscillator where
  lambda : ℝ
  lambda_pos : 0 < lambda

/--
The flow map (right-hand side of the ODE): `f(v) = -λ • v`.
-/
def flowMap (osc : Oscillator) (v : n → ℝ) : n → ℝ :=
  -osc.lambda • v

/--
The explicit solution `x(t) = exp(-λ t) • v₀`.
-/
def solution (osc : Oscillator) (v0 : n → ℝ) (t : ℝ) : n → ℝ :=
  exp (-osc.lambda * t) • v0

/--
Differentiability of the solution in time: its derivative is the flow map.
-/
theorem hasDerivAt_solution (osc : Oscillator) (v0 : n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => solution osc v0 t) (flowMap osc (solution osc v0 t)) t := by
  dsimp [solution, flowMap]
  -- derivative of exp(-λ * t) is (-λ) * exp(-λ * t)
  have h_exp := (hasDerivAt_exp _).const_mul osc.lambda
  -- scaling: derivative of (t ↦ a t) is a.
  have h_mul := (hasDerivAt_const_smul _ _ _).comp t h_exp
  simpa [neg_mul, neg_smul] using h_mul

/--
Norm of the solution decays as ‖x(t)‖ = exp(-λ t) * ‖v0‖.
-/
theorem norm_solution (osc : Oscillator) (v0 : n → ℝ) (t : ℝ) :
    ‖solution osc v0 t‖ = exp (-osc.lambda * t) * ‖v0‖ := by
  dsimp [solution]
  -- norm of scalar multiplication: ‖c • v₀‖ = |c| * ‖v₀‖
  rw [norm_smul, Real.norm_eq_abs]
  -- |exp(-λ t)| = exp(-λ t)
  congr 1
  apply (abs_exp _).symm

/--
Exponential decay bound: ‖x(t)‖ ≤ exp(-λ t) * ‖v0‖.
-/
theorem norm_solution_le (osc : Oscillator) (v0 : n → ℝ) (t : ℝ) :
    ‖solution osc v0 t‖ ≤ exp (-osc.lambda * t) * ‖v0‖ := by
  rw [norm_solution osc v0 t]
  apply le_rfl

/--
The unique invariant state is the zero vector.
If `x(t) = x(0)` for all `t`, then `x(0) = 0`.
-/
theorem unique_invariant (osc : Oscillator) (v0 : n → ℝ)
    (h_inv : ∀ t, solution osc v0 t = v0) : v0 = 0 := by
  specialize h_inv 1
  dsimp [solution] at h_inv
  -- exp(-λ * 1) • v0 = v0 implies (exp(-λ) - 1) • v0 = 0
  have h := congrArg (fun x => x - v0) h_inv
  simp only [smul_sub, sub_self, sub_eq_zero, Pi.sub_apply] at h
  -- (exp(-λ) - 1) ≠ 0 since λ > 0
  have h_ne : exp (-osc.lambda) - 1 ≠ 0 := by
    have h_gt : exp (-osc.lambda) < 1 := by
      apply exp_lt_one_of_neg; linarith [osc.lambda_pos]
    linarith
  -- thus v0 = 0
  simpa [smul_eq_zero] using (smul_eq_zero.1 h).resolve_left (by simpa using h_ne)

end Paralogic.Oscillator
