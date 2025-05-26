import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic

/-!
  src/Paralogic/Frames.lean

  Constraint definitions on a real inner-product space `E`, with
  margin, violation, convexity, and Lipschitz continuity lemmas.
-/


namespace Paralogic.Frames

open InnerProductSpace Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A linear “constraint” on `E` is given by a weight `w : E`, threshold `c : ℝ`,
and nonnegative slack `ε`.
The feasible region is `{v | ⟪w, v⟫ - c ≥ -ε}`.
-/
structure Constraint where
  w : E
  c : ℝ
  ε : ℝ
  eps_nonneg : 0 ≤ ε

namespace Constraint

/-- The signed margin of `v` with respect to the constraint. -/
def margin (C : Constraint) (v : E) : ℝ :=
  ⟪C.w, v⟫ - C.c - C.ε

/-- `v` satisfies the constraint iff `margin C v ≥ 0`. -/
def satisfied (C : Constraint) (v : E) : Prop :=
  0 ≤ C.margin v

/-- The violation amount, zero if satisfied, otherwise `- margin`. -/
def violation (C : Constraint) (v : E) : ℝ :=
  max 0 (- C.margin v)

instance : Inhabited Constraint where
  default := { w := 0, c := 0, ε := 0, eps_nonneg := by simp }

/-- `margin` is an affine function in `v`. -/
theorem margin_affine (C : Constraint) : AffineMap ℝ E ℝ :=
  { toFun := fun v => ⟪C.w, v⟫ - C.c - C.ε
    linear := 
      { toFun := fun v => ⟪C.w, v⟫
        map_add := by intros; simp [inner_add_left]
        map_smul := by intros; simp [inner_smul_left] }
    map_add' := by intros; simp [sub_add, sub_sub]
    map_smul' := by intros; simp [sub_smul, sub_smul, sub_sub] }

/-- `margin` is convex (being affine). -/
theorem margin_convex (C : Constraint) : ConvexOn (univ : Set E) (margin C) :=
  (margin_affine C).convexOn

/-- `margin` is continuous (being affine). -/
theorem margin_continuous (C : Constraint) : Continuous (margin C) :=
  (margin_affine C).continuous

/-- `margin` is Lipschitz with constant `‖C.w‖`. -/
theorem margin_lipschitz (C : Constraint) :
    LipschitzWith ‖C.w‖ (margin C) := by
  -- |⟪w,v⟫ - c - ε - (⟪w,u⟫ - c - ε)| = |⟪w,v - u⟫| ≤ ‖w‖ * ‖v - u‖
  refine ⟨by simp, fun _ _ => by
    have h : |margin C v - margin C u| = |⟪C.w, v - u⟫| := by
      dsimp [margin]; simp [sub_sub, sub_sub]
    simpa [h] using (abs_inner_le_norm_mul_norm _ _).trans_eq rfl⟩

/-- `violation` is the composition of `max 0 ∘ neg` with `margin`, hence convex. -/
theorem violation_convex (C : Constraint) : ConvexOn (univ : Set E) (violation C) := by
  dsimp [violation]
  apply ConvexOn.comp convex_neg (convexOn_const maximZeroOn) (margin_convex C)
  -- `neg : ℝ → ℝ` is affine hence convex, and `max 0` is convex on `ℝ`.
  · exact (AffineMap.neg.constISO.convexOn)
  · exact convexOn_max_left zero_le_one

/-- `violation` is Lipschitz with constant `‖C.w‖`. -/
theorem violation_lipschitz (C : Constraint) :
    LipschitzWith ‖C.w‖ (violation C) := by
  dsimp [violation]
  refine (LipschitzWith.comp _ (margin_lipschitz C)).1.2
  -- `max 0 ∘ neg` has Lipschitz constant 1.
  have : LipschitzWith 1 fun x : ℝ => max 0 (-x) := by
    have : IsLipschitzOn 1 (fun x => max 0 (-x)) univ := by
      simpa only [univ_inter] using (isLipschitzOn_iff_lipschitzWith.2
        { constant := 1
          bound := by intros; simp; exact abs_neg _ })
    exact (lipschitzOn_iff_lipschitzWith.1 this)
  simpa using this.comp (margin_lipschitz C)

end Constraint

end Paralogic.Frames
