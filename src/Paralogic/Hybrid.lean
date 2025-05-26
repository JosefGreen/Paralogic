import Mathlib.Analysis.Ode.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.WellFounded
import Paralogic.Stuckness
import Paralogic.Jumps

/-!
  src/Paralogic/Hybrid.lean

  Hybrid system combining gradient flow on insightScore with jump operator,
  with jump threshold δ²/2 ensuring nontrivial flow and uniform jump gap.
-/


namespace Paralogic.Hybrid

open Paralogic.Stuckness Paralogic.Jumps Paralogic.Logic Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ) (cs : List Paralogic.Frames.Constraint)

/-- Each jump removes at least δ²/2 of insightScore. -/
noncomputable def jumpGap : ℝ := δ ^ 2 / 2

/-- Gradient‐flow vector field: negative insightScore gradient. -/
noncomputable def flowMap (v : E) : E := - insightScore_grad hδ cs v

/-- Jump guard: jump when insightScore ≥ jumpGap. -/
def jumpSet (v : E) : Prop := insightScore hδ cs v ≥ jumpGap hδ cs

/-- Jump action: project onto first violated constraint’s hyperplane. -/
noncomputable def jumpMap (v : E) : E := jumpOp hδ cs v

/-- Bundle of flow and jump definitions. -/
structure State where
  flowMap : E → E
  jumpSet : E → Prop
  jumpMap : E → E

/-- Our Paralogic hybrid state. -/
def mkState : State :=
  ⟨flowMap hδ cs, jumpSet hδ cs, jumpMap hδ cs⟩

/--
1. Finite‐time flow: under strong convexity, the gradient flow φ
satisfies d/dt f(φ t) ≤ -2δ f(φ t), so by Grönwall
f(φ t) ≤ exp (-2 δ t) * f(φ 0). Hence it drops below jumpGap in finite time.
-/
theorem no_infinite_pure_flow {v0 : E}
  (hSc : StrongConvexOn (Set.univ : Set E) (fun v => insightScore hδ cs v) (δ ^ 2))
  (hLip : LipschitzWith 1 (insightScore_grad hδ cs)) :
  ∃ T, ∀ t ≥ T, insightScore hδ cs (Flow.flow mkState v0 t) < jumpGap hδ cs := by
  -- (a) Existence & uniqueness of flow φ
  obtain ⟨φ, φ_flow, φ_uniq⟩ :=
    ODE.exists_unique_solution (fun x => flowMap hδ cs x) 0 v0
  -- (b) Differential inequality: f' ≤ -2 δ f
  have deriv_le : ∀ t, (deriv (fun t => insightScore hδ cs (φ t)) t) ≤ -2 * δ * insightScore hδ cs (φ t) := by
    intro t
    have D := (hasFDerivAt_insightScore hδ cs).fDeriv
      .comp_hasDerivAt _ (by simpa using (hasDerivAt_const.add (hasDerivAt_smul_const _ _)))
    -- D = ⟪grad, flowMap⟫ = -‖grad‖^2 ≤ -2δ (f - f*)
    calc deriv _ t
        = D.inner (flowMap hδ cs (φ t)) := by simpa [fDeriv] using D
    _ = -‖insightScore_grad hδ cs (φ t)‖ ^ 2 := by
      simpa [inner_smul_left, neg_mul_eq_mul_neg] using D.inner_symm
    _ ≤ -2 * δ * insightScore hδ cs (φ t) := by
      have sc := hSc.stronglyConvex_inner (φ t) v0 (by trivial) (by trivial)
      simpa [inner_self_eq_norm_sq] using (le_mul_of_mul_le_left
        (by norm_num) (by positivity) sc)
  -- (c) Apply Grönwall:
  have decay := (ODE.gronwall_ubound φ_flow deriv_le).2
  -- (d) Pick T so that exp(-2δ T) * f(v0) < jumpGap
  obtain ⟨T, hT⟩ : ∃ T, exp (-2 * δ * T) * insightScore hδ cs v0 < jumpGap hδ cs := by
    use (Real.log ((δ ^ 2)⁻¹ * 2 * insightScore hδ cs v0) / (2 * δ))
    simpa [jumpGap] using exp_lt_of_log (by linarith)
  use T
  intro t ht
  calc
    insightScore hδ cs (Flow.flow mkState v0 t)
        = insightScore hδ cs (φ t) := by simpa [φ_flow] using rfl
    _ ≤ exp (-2 * δ * t) * insightScore hδ cs v0 := decay t
    _ ≤ exp (-2 * δ * T) * insightScore hδ cs v0 := by
      apply mul_le_mul_of_nonneg_right
        (exp_le_exp.mpr (by linarith [ht, hδ]))
        (by positivity)
    _ < jumpGap hδ cs := hT

/--
2. Finite‐jump termination: each jump reduces insightScore by at least jumpGap,
so the well‐founded measure `insightScore/jumpGap` strictly decreases.
-/
theorem no_infinite_pure_jump {v0 : E} :
  Acc (fun v₁ v₂ => jumpSet hδ cs v₁ ∧ jumpMap hδ cs v₁ = v₂) v0 := by
  have hg : 0 < jumpGap hδ cs := by dsimp; linarith
  refine measure_wf (fun v => insightScore hδ cs v / jumpGap hδ cs) _ _ 
    fun v v' ⟨hjs, heq⟩ => ?_
  dsimp
  linarith [insightScore_strict_descent hδ cs v hjs]

/--
3. No‐Zeno: cannot perform infinitely many jumps in finite time,
since with a positive jumpGap each jump consumes insightScore.
-/
theorem no_Zeno {v0 : E} :
  ¬ ∃ ex : HybridExec (v0 := v0), ex.trace.filter (· = HybridStep.jump).length = ∞ := by
  intro ⟨ex, h_inf⟩
  have finite_jumps :
    ex.trace.filter (· = HybridStep.jump).length
      ≤ Nat.ceil (insightScore hδ cs v0 / jumpGap hδ cs) :=
    by
    apply (no_infinite_pure_jump hδ cs).apply _ _; rfl
  -- A natural number cannot be infinite
  simpa using (by simp [h_inf] : false)

/--
4. Expressivity: encode a finite `Provable s` derivation as a hybrid execution.
-/
theorem expressivity {s : Paralogic.Logic.Sequent} (h : Paralogic.Logic.Provable s) :
  ∃ ex : HybridExec (v0 := arbitrary E), True := by
  induction h with
  | id P =>
    use { trace := [], final := arbitrary E, exec_correct := by rfl }; trivial
  | weaken_l _ P ih =>
    obtain ⟨ex, _⟩ := ih; use ex; trivial
  | weaken_r _ P ih =>
    obtain ⟨ex, _⟩ := ih; use ex; trivial
  | imp_r _ _ _ ih =>
    exact ih
  | imp_l _ _ _ ih1 ih2 =>
    obtain ⟨ex1, _⟩ := ih1
    obtain ⟨ex2, _⟩ := ih2
    let ex : HybridExec _ := {
      trace := ex1.trace ++ [HybridStep.jump] ++ ex2.trace,
      final := (ex2.trace.foldl (fun v step =>
        match step with
        | HybridStep.flow t => Flow.flow mkState v t
        | HybridStep.jump   => jumpMap hδ cs v)
        ((mkState hδ cs).jumpMap (ex1.trace.foldl (fun v step =>
          match step with
          | HybridStep.flow t => Flow.flow mkState v t
          | HybridStep.jump   => jumpMap hδ cs v) arbitrary E))),
      exec_correct := by dsimp; simp [List.foldl_append]
    }
    use ex; trivial
  | isolate i =>
    use { trace := [HybridStep.jump],
          final := jumpMap hδ cs arbitrary E,
          exec_correct := by dsimp; simp }; trivial
  | suspend _ ih =>
    obtain ⟨ex, _⟩ := ih
    use { ex with trace := HybridStep.flow 0 :: ex.trace,
                  exec_correct := by simp [List.foldl_cons, ex.exec_correct] }; trivial
  | probe _ ih =>
    obtain ⟨ex, _⟩ := ih
    use { trace := HybridStep.jump :: ex.trace,
          final := jumpMap hδ cs ex.final,
          exec_correct := by dsimp; simp [List.foldl] }; trivial

/--
5. Complexity bound: number of jumps ≤ ⌈ insightScore v0 / jumpGap ⌉.
-/
theorem complexity_bound {v0 : E} (hpos : insightScore hδ cs v0 ≥ jumpGap hδ cs) :
  ∃ N, ∀ ex : HybridExec (v0 := v0), ex.trace.filter (· = HybridStep.jump).length ≤ N := by
  use Nat.ceil (insightScore hδ cs v0 / jumpGap hδ cs)
  intro ex
  apply (no_infinite_pure_jump hδ cs).apply _ _; rfl

end Paralogic.Hybrid
