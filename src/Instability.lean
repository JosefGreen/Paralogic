import Paralogic.Stuckness
import Paralogic.Entropy
import Paralogic.Jumps
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
  src/Paralogic/Instability.lean

  Metrics for “instability” and a simple “revolution” operator
  within the Paralogic ecosystem.

  • Prove nonnegativity of `insightScore` and `frameEntropy`.
  • Define `instabilityScore` combining them.
  • Define `revolutionSet` and `revolutionOp`.
  • Prove `instabilityScore_nonneg`.
-/


namespace Paralogic.Instability

open Paralogic.Stuckness Paralogic.Entropy Paralogic.Jumps Real List

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ) (cs : List Paralogic.Frames.Constraint)

/-- `insightScore` is always ≥ 0, since it’s a sum of nonnegative Huber penalties. -/
theorem insightScore_nonneg (v : E) : 0 ≤ insightScore hδ cs v := by
  dsimp [insightScore]
  apply sum_nonneg
  intro C _
  dsimp [huber, margin]
  split_ifs with h'
  · exact mul_self_nonneg _
  · have hm : |margin C v| > δ := by simpa [margin] using (not_le.mp h')
    have hpos : δ * |margin C v| > δ * δ := mul_lt_mul_of_pos_left hm (hδ)
    linarith

/-- `frameEntropy` is always ≥ 0 for a valid probability distribution. -/
theorem frameEntropy_nonneg (v : E) : 0 ≤ frameEntropy hδ cs v := by
  dsimp [frameEntropy]
  let p := violationProb hδ cs v
  have sum_neg :
    -(p.map fun pi => if pi = 0 then 0 else pi * log pi).sum
      = (p.map fun pi => if pi = 0 then 0 else -(pi * log pi)).sum := by
    simpa using sum_map_neg (fun pi => if pi = 0 then 0 else pi * log pi) p
  rw [sum_neg]
  apply sum_nonneg
  intro pi _
  dsimp
  split_ifs with h0
  · simp
  · have pitpos : 0 < pi := by
      dsimp [violationProb] at h0; split_ifs at h0 with hm; · simp [hm] at h0; linarith; ·
      have mpos := (totalMass hδ cs v).pos; simpa [hm] using div_pos (by linarith) (by linarith)
    have pi_le_one : pi ≤ 1 := by
      dsimp [violationProb] at h0
      have mpos := (totalMass hδ cs v).pos
      have raw_le : max 0 (- margin C v) ≤ totalMass hδ cs v := by
        dsimp [totalMass, rawViolations]; apply single_le_sum; simp; linarith
      simpa [h0] using div_le_one_of_le (le_of_lt mpos) raw_le
    have log_nonpos : log pi ≤ 0 := log_le_zero pitpos.le pi_le_one
    calc -(pi * log pi) ≥ -(pi * 0) := by
      apply neg_le_neg; apply mul_le_mul_of_nonneg_left log_nonpos (by linarith)
    simp

/--
Weights for combining insight and entropy into a single instability metric.
-/
structure Weights where
  α  : ℝ
  β  : ℝ
  ha : 0 < α
  hb : 0 < β

/--
The instability score of a state `v`:
```
instabilityScore v = α * insightScore v + β * frameEntropy v
```
-/
def instabilityScore (w : Weights) (v : E) : ℝ :=
  w.α * insightScore hδ cs v + w.β * frameEntropy hδ cs v

/--
When the insightScore alone exceeds the jump-gap, we declare a “revolution”.
-/
def revolutionSet (v : E) : Prop :=
  insightScore hδ cs v ≥ δ^2 / 2

/--
A revolution operator that applies the Paralogic jump.
-/
noncomputable def revolutionOp (v : E) : E :=
  jumpOp hδ cs v

/--
Instability score is always nonnegative.
-/
theorem instabilityScore_nonneg (w : Weights) (v : E) :
  0 ≤ instabilityScore hδ cs w v := by
  dsimp [instabilityScore]
  apply add_nonneg
  · exact mul_nonneg (le_of_lt w.ha) (insightScore_nonneg hδ cs v)
  · exact mul_nonneg (le_of_lt w.hb) (frameEntropy_nonneg hδ cs v)

end Paralogic.Instability
