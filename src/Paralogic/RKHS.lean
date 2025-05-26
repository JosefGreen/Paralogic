import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Data.Finset.Basic
import Paralogic.Basic

/-!
  src/Paralogic/RKHS.lean

  Reproducing‐Kernel Hilbert Space as the completion of the algebraic span
  of representers, with the reproducing property fully formalized.
-/


namespace Paralogic.RKHS

variable {α : Type*} (k : Kernel α) [hK : IsPosDefKernel k]

/-- The representer at a point `x`: the function `i ↦ k i x`. -/
def representer (x : α) : α → ℝ := fun i => k i x

/-- The algebraic span of all representers. -/
def algSpan : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ (Set.range (representer k))

/-- The RKHS is the Hilbert‐space completion of the algebraic span. -/
def RKHS : Type* := Completion (algSpan k)

/-- Inclusion of the span into its completion. -/
def toRKHS (f : algSpan k) : RKHS k := Completion.mk f

instance : InnerProductSpace ℝ (RKHS k) :=
  Completion.innerProductSpace _

/-- Embed a kernel‐function representer into the RKHS. -/
def embed (x : α) : RKHS k :=
  toRKHS k ⟨representer k x, Submodule.subset_span (Set.mem_range_self x)⟩

/--
Reproducing property: for any `f : algSpan k`,
the inner product with the representer at `x` recovers `f.val x`.
-/
theorem reproducing (f : algSpan k) (x : α) :
    Completion.inner (toRKHS k f) (embed k x) = f.val x := by
  -- Expand definitions of `toRKHS` and `embed`
  dsimp [toRKHS, embed]
  -- Reduce `Completion.inner` on two `mk` to the inner on the span
  simp only [Completion.inner_mk]
  -- Now we must show `Submodule.inner f (⟨representer k x, _⟩ : algSpan k) = f.val x`
  dsimp [Submodule.inner]
  -- Unfold the algebraic IP: ∑ i j, f.val i * k i j * (representer k x) j
  dsimp [ip, representer]
  -- Decompose `f` as a finite linear combination of representers
  rcases f.memSpan with ⟨s, a, rfl⟩
  -- Now `f.val j = ∑ m in s, a m * k m j`
  -- Thus the inner product becomes:
  --   ∑ i j, (∑ m in s, a m * k m i) * k i j * k j x
  -- Swap sums to group by m then j
  calc
    ∑ i in Finset.univ, ∑ j in Finset.univ, (∑ m in s, a m * k m i) * k i j * k j x
        = ∑ m in s, a m * ∑ j in Finset.univ, k m j * k j x := by
      simp [Finset.sum_comm, Finset.sum_mul, Finset.mul_sum]
  _   = ∑ m in s, a m * representer k x m := by
      simp [representer]
  _   = (fun j => ∑ m in s, a m * k m j) x := by
      dsimp [FunLike.coe, Subtype.val]; rfl
  -- The final expression is exactly `f.val x`
  rfl

end Paralogic.RKHS
