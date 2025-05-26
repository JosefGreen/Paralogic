import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.FDeriv
import Mathlib.Analysis.Calculus.FDeriv
import Paralogic.Frames
import Paralogic.Stuckness
import Paralogic.Jumps

/-!
  src/Paralogic/AnalysisExtras.lean

  Analytical lemmas for Paralogic:
  • Strict concavity of `-t log t`.
  • Strict sum‐monotonicity for one‐coordinate changes.
  • Full Fréchet‐derivative of `frameEntropy` via chain‐rule, including margin derivative.
-/

open Real List
open Paralogic.Frames Paralogic.Stuckness Paralogic.Jumps Paralogic.Entropy

namespace Paralogic.AnalysisExtras

/-- The derivative of the margin function is the inner‐product with the constraint weight. -/
theorem hasFDerivAt_margin
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Constraint) (v : E) :
  HasFDerivAt (fun w => margin C w) (continuousLinearMap.inner ℝ E C.w) v := by
  dsimp [margin]
  exact (continuousLinearMap.inner ℝ E C.w).hasFDerivAt

/-- The zero function has derivative zero. -/
theorem hasFDerivAt_zero
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : E) :
  HasFDerivAt (fun _ : E => 0) (0 : E →L[ℝ] ℝ) v :=
  (hasFDerivAt_const _ 0 v).const_smul _

/-- Strict concavity of `λ t, -t * log t` on `[0,1]`. -/
theorem neg_mul_log_strictConcaveOn_Icc :
    StrictConcaveOn (Set.Icc 0 1) (fun t => -t * log t) := by
  refine strictConcaveOn_of_deriv2_neg (fun t ht => _)
  have h1 : deriv (fun x => -x * log x) t = -log t - 1 := by
    simpa using (deriv_mul (by continuity) (by continuity) t).neg
  have h2 : deriv (fun x => -log x - 1) t = -1 / t := by
    simpa using (deriv_sub (by continuity) (by continuity) t)
  simpa [h1] using h2

/--
If two lists `p` and `q` differ only at index `i` with `p i < q i`, and `f` is strictly concave,
then `∑ f (p)` < `∑ f (q)`.
-/
theorem sumStrictMono {α : Type*} [DecidableEq α] {l : List α}
  {p q : α → ℝ} {i : α} (h₁ : p i < q i)
  (h₂ : ∀ j, j ≠ i → p j = q j)
  {f : ℝ → ℝ} (hf : StrictConcaveOn (range (l.map p) ∪ range (l.map q)) f) :
  (l.sum fun j => f (p j)) < (l.sum fun j => f (q j)) := by
  induction l with
  | nil      => simpa using h₁
  | cons j tl ih =>
    simp only [sum_cons]
    by_cases hji : j = i
    · subst hji
      have : f (p i) < f (q i) := hf.lt_iff.mpr h₁
      simpa using add_lt_add_left this _
    · have hpq := h₂ j hji
      simp [hpq] at ih
      simpa [hpq] using ih

open ContinuousLinearMap

/--
Fréchet‐derivative of `frameEntropy` at `v` is the linear functional
`H ↦ ⟪entropy_grad hδ cs v, H⟫`.
-/
theorem hasFDerivAt_frameEntropy
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {δ : ℝ} (hδ : 0 < δ) (cs : List Constraint) (v : E) :
  HasFDerivAt (frameEntropy hδ cs)
    (inner ℝ E (entropy_grad hδ cs v)) v := by
  -- Unfold definitions
  dsimp [frameEntropy, violationProb, rawViolations]
  apply HasFDerivAt.neg
  apply HasFDerivAt.sum
  intro C hC
  -- Let π_C(w) = violation C w / totalMass w
  let π : E → ℝ := fun w => violation C w / totalMass hδ cs w
  -- Derivative of π by quotient rule
  have dπ : HasFDerivAt π
    ((continuousLinearMap.inner ℝ E C.w) / totalMass hδ cs v
     - (violation C v) • (continuousLinearMap.inner ℝ E (∑ D in cs, D.w)) / (totalMass hδ cs v)^2)
    v := by
    apply HasFDerivAt.div
    -- numerator: violation C w = max 0 (-margin C w)
    · apply (hasFDerivAt_const_mul _ _).sub (hasFDerivAt_const_mul _ _)
      · exact (hasFDerivAt_zero v)
      · exact (hasFDerivAt_margin C v).const_mul _
    -- denominator: totalMass w = ∑ D, violation D w
    refine (HasFDerivAt.sum _ _).2 fun D hD => (hasFDerivAt_const_mul _ _)
  -- Derivative of log at π v
  have dlog : HasFDerivAt (fun x => x.log) (1 / π v) (π v) := by
    apply HasFDerivAt.log
    dsimp [π]; split_ifs with h
    · simpa [h] using (by linarith [totalMass_nonneg hδ cs v])
    · apply div_pos
      · exact (by linarith [totalMass_nonneg hδ cs v])
      · linarith [totalMass_pos_of_jumpGap hδ cs v]
  -- Combine π' * log π v + π v • (1/π v) • π'
  refine (dπ.mul_const (log (π v))).add _
  have term := dπ.const_mul (π v / (π v))
  simpa using term.comp_hasFDerivAt _ dlog

end Paralogic.AnalysisExtras
