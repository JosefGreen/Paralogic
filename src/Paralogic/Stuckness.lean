import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.FDeriv
import Paralogic.Frames
import Paralogic.Basic  -- for `huber`

/-!
  src/Paralogic/Stuckness.lean

  The insight score: a sum of Huber‐penalized margins on an inner‐product space,
  with convexity, continuity, differentiability, and an explicit gradient.
-/


namespace Paralogic.Stuckness

open InnerProductSpace ContinuousLinearMap Paralogic.Frames Constraint Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ)

/--
The insight‐score is the sum of Huber penalties on each constraint’s margin.
-/
noncomputable def insightScore (cs : List Constraint) (v : E) : ℝ :=
  cs.sum fun C => huber hδ (margin C v)

/--
Convexity of `insightScore` on all of `E`.
-/
theorem insightScore_convex (cs : List Constraint) :
    ConvexOn (Set.univ : Set E) (insightScore hδ cs) :=
  cs.convexOn_sum (fun _ => (huber_convex (hδ := hδ)).restrict _)

/--
Continuity of `insightScore`.
-/
theorem insightScore_continuous (cs : List Constraint) :
    Continuous (insightScore hδ cs) :=
  cs.continuous_sum (fun _ => huber_continuous (hδ := hδ))

/--
The gradient of `insightScore` at `v` is the weighted sum of constraint weights:
```
∇_v = ∑ C in cs,
        (if |m| ≤ δ then m else δ * sign m) • C.w
where m = margin C v.
```
-/
noncomputable def insightScore_grad (cs : List Constraint) (v : E) : E :=
  cs.sum fun C =>
    let m := margin C v
    let α := if |m| ≤ δ then m else δ * m.sign
    α • C.w

/--
`insightScore` is differentiable everywhere.
-/
theorem insightScore_differentiable (cs : List Constraint) :
    Differentiable ℝ (insightScore hδ cs) := by
  apply differentiable_sum; intros C
  have A : Differentiable ℝ fun x => margin C x := by
    refine (differentiable_const.sub_const).add_const.sub_const
    exact (continuousLinearMap.inner _).differentiable
  have B : Differentiable ℝ (huber hδ ∘ margin C) :=
    (huber_continuous (hδ := hδ)).differentiable.comp A
  exact B

/--
Explicit Fréchet‐derivative of `insightScore` at `v`.
-/
theorem hasFDerivAt_insightScore (cs : List Constraint) (v : E) :
    HasFDerivAt (insightScore hδ cs)
      (∑ C in cs, (if |margin C v| ≤ δ then margin C v else δ * (margin C v).sign) •
           (continuousLinearMap.inner ℝ E C.w)) v := by
  apply (hasFDerivAt_sum _ cs).2; intros C hC
  have Dm := (continuousLinearMap.inner ℝ E C.w).hasFDerivAt
  have Dh := (huber_deriv _ _ (Or.inl (by
    have : |margin C v| ≠ δ := by
      intro h; simpa [h] using (hδ.ne').symm
    by simpa using hδ.ne')).hasFDerivAt
  simpa [Function.comp] using Dh.comp v Dm

/--
The derivative map is represented by the inner‐product with `insightScore_grad`.
-/
theorem fDeriv_insightScore_eq_inner (cs : List Constraint) (v : E) :
    fDeriv ℝ (insightScore hδ cs) v =
      continuousLinearMap.inner ℝ E (insightScore_grad hδ cs v) := by
  have := (hasFDerivAt_insightScore _ _).fDeriv
  simpa [insightScore_grad, fDeriv] using this

end Paralogic.Stuckness
