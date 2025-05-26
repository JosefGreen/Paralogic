import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Instances.Real

/-!
  src/Paralogic/Basic.lean

  Core definitions: Huber tension, paraconsistent preservation, RKHS as algebraic span,
  reproducing‐kernel lemma in the algebraic setting.
-/

namespace Paralogic.Basic

open Real

variable {α : Type*}

/-- The Huber penalty with threshold δ. -/
def huber (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ℝ :=
  if |x| ≤ δ then x^2 / 2 else δ * |x| - δ^2 / 2

/-- Simplest reproducing‐kernel Hilbert space setup as algebraic span. -/
structure Kernel where
  toFun : α → α → ℝ

instance : CoeFun (Kernel α) fun k => α → α → ℝ := ⟨Kernel.toFun⟩

class IsPosDefKernel (k : Kernel α) : Prop where
  symm : ∀ i j, k i j = k j i
  pos  : ∀ f : α → ℝ, 0 ≤ ∑ i j, f i * k i j * f j
  eq0  : ∀ {f}, (∑ i j, f i * k i j * f j = 0) → f = 0

variable (k : Kernel α) [hK : IsPosDefKernel k]
include hK

/-- Induced inner product on `α → ℝ`. -/
noncomputable def ip (f g : α → ℝ) : ℝ := ∑ i j, f i * k i j * g j

/-- Register as an inner product space. -/
noncomputable instance toInnerProductSpace : InnerProductSpace ℝ (α → ℝ) where
  inner := ip k
  conj_sym := by intros; simp [ip, IsPosDefKernel.symm (k := k)]
  add_left := by intros; simp [ip]
  smul_left := by intros; simp [ip]
  norm_sq_eq_inner := fun f => by
    simp [ip, IsPosDefKernel.pos (k := k) f, Real.inner_self_eq_norm_sq]

/-- Representer at `x`: `i ↦ k i x`. -/
def representer (x : α) : α → ℝ := fun i => k i x

/-- RKHS as algebraic span of representers. -/
def RKHS : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ (Set.range (representer k))

/-- Every representer lies in the span. -/
theorem representer_mem (x : α) : representer k x ∈ RKHS k :=
  Submodule.subset_span (Set.mem_range_self x)

/-- Reproducing property on the algebraic span:
    if `f = ∑ i in s, a i • representer i`, then `<f, representer x> = f x`. -/
theorem reproducing_finset {s : Finset α} {a : α → ℝ} :
  let f : α → ℝ := fun j => ∑ i in s, a i * k i j
  ∀ x, InnerProductSpace.inner f (representer k x) = f x := by
  -- expand definitions and swap sums
  intro f x
  dsimp [representer, ip]; simp only [Finset.sum_mul]
  have swap : ∑ (j i) in Finset.univ.product s, a i * k i j * k j x
           = ∑ (i j) in s.product Finset.univ, a i * k i j * k j x := by
    simpa [mul_comm] using (Finset.sum_comm (s.product Finset.univ) (fun ij => a ij.1 * k ij.1 ij.2 * k ij.2 x))
  simp [swap]
  -- use symmetry k j i = k i j
  simp [IsPosDefKernel.symm (k := k)]
  -- group sums to get f x
  rfl

end Paralogic.Basic
