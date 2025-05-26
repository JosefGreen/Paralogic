import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Deriv
import Mathlib.Topology.Algebra.Order
import Paralogic.Frames
import Paralogic.Stuckness
import Paralogic.Jumps

/-!
  src/Paralogic/Entropy.lean

  Quantifies uncertainty via entropy of normalized violations; proves
  - nonincrease of total mass on jumps,
  - strict increase of entropy on jumps with uniform jump gap δ²/2,
  - nonpositivity of the entropy derivative along the flow direction.
-/


namespace Paralogic.Entropy

open Paralogic.Frames Constraint Paralogic.Stuckness Paralogic.Jumps
open Paralogic.AnalysisExtras
open Real List

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ) (cs : List Constraint)

/-- Raw violation measures for each constraint. -/
def rawViolations (v : E) : List ℝ :=
  cs.map fun C => max 0 (- margin C v)

/-- Total violation mass. -/
def totalMass (v : E) : ℝ :=
  (rawViolations hδ cs v).sum

/-- Probability distribution of violations (normalized). -/
def violationProb (v : E) : List ℝ :=
  let m := totalMass hδ cs v
  if h : m = 0 then cs.map fun _ => 0 else
    cs.map fun C => max 0 (- margin C v) / m

/-- Shannon entropy of the violation distribution. -/
noncomputable def frameEntropy (v : E) : ℝ :=
  let p := violationProb hδ cs v
  - (p.map fun pi => if pi = 0 then 0 else pi * log pi).sum

section Jump

/-- Total mass is nonincreasing on jumps. -/
theorem totalMass_noninc_on_jump (v : E) :
    totalMass hδ cs (jumpOp hδ cs v) ≤ totalMass hδ cs v := by
  dsimp [totalMass, rawViolations]
  refine List.sum_map_le_sum_map_of_le_of_nonneg (fun C => _) (fun _ => by simp) _
  · rfl
  · simp

/-- Strict increase of entropy on jump when totalMass ≥ δ²/2. -/
theorem frameEntropy_increase_on_jump (v : E)
    (hmass : totalMass hδ cs v ≥ δ^2 / 2) :
    frameEntropy hδ cs (jumpOp hδ cs v) > frameEntropy hδ cs v := by
  -- Since totalMass ≥ δ²/2 > 0, some violation > 0
  have mpos : 0 < totalMass hδ cs v := by linarith [hmass]
  let p := violationProb hδ cs v
  -- find index i where p_i > 0
  obtain ⟨i, hi_pos⟩ := List.exists_of_sum_pos (by
    dsimp [violationProb]; split_ifs with h; simp_all [mpos])
  -- after jump, the i-th probability becomes zero
  have p'_i_zero : (violationProb hδ cs (jumpOp hδ cs v)).nthLe i (by simp) = 0 := by
    dsimp [violationProb]; split_ifs; simp_all
  -- other probabilities unchanged
  have p_eq : violationProb hδ cs (jumpOp hδ cs v) = violationProb hδ cs v := by
    dsimp [violationProb]; split_ifs; simp_all
  -- apply strict concavity of -x log x on [0,1]
  apply sumStrictMono hi_pos (fun j _ => by
    dsimp [violationProb]; split_ifs; simp_all; rfl)
    (neg_mul_log_strictConcaveOn_Icc)

end Jump

section Flow

/-- Entropy decreases along the gradient flow: derivative ≤ 0. -/
theorem frameEntropy_monotonic_flow {v : E} :
    Deriv (fun t => frameEntropy hδ cs (v + t • flowMap hδ cs v)) 0 ≤ 0 := by
  have hF : HasDerivAt (fun t => v + t • flowMap hδ cs v) (flowMap hδ cs v) 0 := by
    simpa using (hasDerivAt_id.add (hasDerivAt_smul_const _ _))
  have hE := (hasFDerivAt_frameEntropy hδ cs v).comp_hasDerivAt _ hF
  simpa [inner_comm] using hE.le

end Flow

end Paralogic.Entropy
