import Mathlib.Data.Fin
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Submodule
import Mathlib.Topology.Algebra.Module
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidt
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
  src/Paralogic/Emanance.lean

  Definition of Frame: closed k-dimensional subspace of ℝ^n.
  Theorems: existence of orthonormal basis, projection operator with self-projection,
  linearity, idempotence, orthogonality, and norm bounds.
-/


namespace Paralogic.Emanance

open Submodule InnerProductSpace GramSchmidt

variable {n k : ℕ}

/-- A Frame is a closed k-dimensional subspace of ℝ^n. -/
structure Frame where
  toSubmodule : Submodule ℝ (Fin n → ℝ)
  [finiteDim : FiniteDimensional ℝ toSubmodule]
  (rank_eq : Module.rank ℝ toSubmodule = k)
  (closed : IsClosed (toSubmodule : Set (Fin n → ℝ)))

attribute [instance] Frame.finiteDim

/-- Every Frame admits an orthonormal basis. -/
theorem Frame.exists_orthonormal_basis (F : Frame) :
    ∃ (b : Basis (Fin k) ℝ F.toSubmodule), Orthonormal ℝ (λ i, b i : Fin n → ℝ) := by
  haveI : NormedAddCommGroup F.toSubmodule := inferInstance
  haveI : InnerProductSpace ℝ F.toSubmodule := inferInstance
  exact GramSchmidt.exists_orthonormal_basis ℝ F.toSubmodule

/-- Projection onto a Frame via an orthonormal basis. -/
noncomputable def Frame.project (F : Frame) (v : Fin n → ℝ) : F.toSubmodule := by
  obtain ⟨b, hb⟩ := F.exists_orthonormal_basis
  exact ∑ i, (⟪v, b i⟫ : ℝ) • b i

/-- A frame projection is idempotent on its subspace. -/
theorem Frame.project_eq_self (F : Frame) {v : Fin n → ℝ} (hv : v ∈ F.toSubmodule) :
  (F.project v : Fin n → ℝ) = v := by
  obtain ⟨b, hb⟩ := F.exists_orthonormal_basis
  let x := ⟨v, hv⟩
  have repr_eq : ∀ i, b.repr x i = ⟪v, b i⟫ := by intro i; exact hb.2.repr_eq_inner x i
  calc ∑ i, (⟪v, b i⟫ : ℝ) • b i
      = ∑ i, (b.repr x i) • b i := by congr; funext; rw repr_eq
  _    = x := by exact b.sum_repr x
  _    = v := rfl

/-- Projection is linear: preserves addition. -/
theorem Frame.project_add (F : Frame) (v w : Fin n → ℝ) :
  F.project (v + w) = F.project v + F.project w := by
  simp [Frame.project, add_inner, add_smul, add_eq_add]

/-- Projection is linear: preserves scalar multiplication. -/
theorem Frame.project_smul (F : Frame) (a : ℝ) (v : Fin n → ℝ) :
  F.project (a • v) = a • F.project v := by
  simp [Frame.project, smul_inner, smul_smul]

/-- Assemble projection as a linear map. -/
def Frame.projLinearMap (F : Frame) : (Fin n → ℝ) →ₗ[ℝ] F.toSubmodule where
  toFun := F.project
  map_add := F.project_add F
  map_smul := F.project_smul F

/-- The decomposition v = project v + (v - project v) is orthogonal. -/
theorem Frame.proj_orthogonal (F : Frame) (v : Fin n → ℝ) :
  ⟪(F.project v : Fin n → ℝ), v - F.project v⟫ = 0 := by
  obtain ⟨b, hb⟩ := F.exists_orthonormal_basis
  have : F.project v = ∑ i, (⟪v,b i⟫ : ℝ) • b i := rfl
  simp [this]
  calc ⟪∑ i, (⟪v,b i⟫ : ℝ) • b i, v - F.project v⟫
      = ∑ i, (⟪v, b i⟫ * ⟪b i, v - F.project v⟫) := by simp [inner_sum_left, sum_mul]
  _   = ∑ i, (⟪v, b i⟫ * (⟪b i, v⟫ - ⟪b i, F.project v⟫)) := by simp [inner_sub_left]
  _   = ∑ i, (⟪v, b i⟫ * (⟪v, b i⟫ - ⟪v, b i⟫)) := by simp [hb.2.inner_left]  
  _   = 0 := by simp

/-- Projection decreases norm: ‖P v‖ ≤ ‖v‖. -/
theorem Frame.norm_project_le (F : Frame) (v : Fin n → ℝ) :
  ‖(F.project v : Fin n → ℝ)‖ ≤ ‖v‖ := by
  have h := F.proj_orthogonal v
  calc ‖F.project v‖ ^ 2 = ⟪F.project v, F.project v⟫ := by simp [norm_eq_inner]
  _ ≤ ⟪F.project v, F.project v⟫ + ⟪v - F.project v, v - F.project v⟫ := by linarith [inner_self_nonneg _]
  _ = ‖v‖ ^ 2 := by simp [norm_eq_inner, add_comm]
  then show ‖F.project v‖ ≤ ‖v‖ := by simpa using (sqrt_le_sqrt (add_nonneg inner_self_nonneg _))

end Paralogic.Emanance
