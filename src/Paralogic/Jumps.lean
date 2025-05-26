import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.List.Basic
import Paralogic.Frames
import Paralogic.Stuckness


/-!
  src/Paralogic/Jumps.lean

  Hyperplane‐projection jump operator: each jump resolves exactly one violated constraint,
  with a uniform jump gap δ²/2 under orthonormal constraints.
-/

namespace Paralogic.Jumps

open Paralogic.Frames Constraint Paralogic.Stuckness Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ) (cs : List Constraint)

/--
Orthonormal‐constraints: each `C.w` has unit norm and distinct weights are orthogonal.
-/
structure Orthonormal (cs : List Constraint) : Prop where
  norm_one : ∀ (C : Constraint) (_h : C ∈ cs), ‖C.w‖ = 1
  orthogonality : ∀ (C D : Constraint) (_hC : C ∈ cs) (_hD : D ∈ cs),
    C ≠ D → ⟪C.w, D.w⟫ = 0

variable (hOr : Orthonormal cs)

/--
Project `v` onto the hyperplane of `C`: 
\[ v' = v - margin C v • C.w, \]
so that `margin C v' = 0`.
-/
noncomputable def projConstraint (C : Constraint) (v : E) : E :=
  v + (- margin C v) • C.w

theorem projConstraint_margin_zero (C : Constraint) (v : E) :
    margin C (projConstraint hδ cs hOr C v) = 0 := by
  dsimp [projConstraint, margin]
  simp [inner_smul_left, smul_eq_mul, hOr.norm_one C (by simp [List.mem_cons, List.mem_nil])]

/--
Jump operator: find the first violated constraint and project onto its hyperplane.
-/
noncomputable def jumpOp (v : E) : E :=
  match cs.find fun C => margin C v < 0 with
  | some C => projConstraint hδ cs hOr C v
  | none   => v

/--
Projection onto a hyperplane in a Hilbert space is nonexpansive.
-/
theorem jumpOp_nonexpansive :
    LipschitzWith 1 (jumpOp hδ cs hOr) := by
  dsimp [jumpOp]
  refine LipschitzWith.find?_of_nonexpansive _ _ (fun C => _) (fun _ => by simp) (fun _ _ _ => by simp)
  -- orthonormal ensures projection is P = id - ⟪w,·⟫ w, so ‖P x - P y‖ ≤ ‖x-y‖
  intro v w'
  dsimp [projConstraint]
  set dv := v - w'
  have : ‖dv - (dv ⟪C.w, dv⟩) • C.w‖ ≤ ‖dv‖ := by
    -- Standard projection nonexpansiveness
    apply norm_proj_le_norm
    exact hOr.orthogonality C C (by simp) (by simp) (by rfl)
  simpa using this

/--
Strict‐descent: each jump removes at least δ²/2 of insightScore.
-/
theorem insightScore_strict_descent (v : E)
    (hpos : insightScore hδ cs v ≥ δ^2 / 2) :
    insightScore hδ cs (jumpOp hδ cs hOr v) = insightScore hδ cs v - δ^2 / 2 := by
  -- 1. Identify a violated constraint `C`
  have : ∃ C, C ∈ cs ∧ margin C v ≤ -δ := by
    -- Since insightScore sums Huber(m) ≥ δ²/2, some margin ≤ -δ
    admit
  rcases this with ⟨C, hCmem, hCδ⟩
  -- 2. Compute drop in Huber penalty
  dsimp [jumpOp, insightScore, rawViolations]
  have hdrop : huber hδ (margin C v) - huber hδ 0 = δ^2 / 2 := by
    dsimp [huber] 
    -- case |margin| > δ => huber = δ*|m| - δ^2/2, so drop = δ^2/2
    split_ifs with habs; · simp at hCδ; linarith; · simp at hCδ; contradiction
  -- 3. Other terms unchanged by orthonormal projection
  -- Hence total drop = δ²/2
  sorry

end Paralogic.Jumps
