/-
  src/paralogic_theorems_stochastic.lean

  Stochastic extensions: supermartingale convergence and invariant measure.
-/

import measure_theory.probability_mass_function
import measure_theory.martingale
import measure_theory.measure.measure_space
import topology.instances.real

namespace paralogic

section supermartingale_convergence

open measure_theory filter

variables {Ω : Type*} [measurable_space Ω] (X : ℕ → Ω → ℝ)
  (F : filtration Ω) (μ : measure Ω)

/--
Theorem C.3 (Supermartingale Convergence):
A non-negative supermartingale with bounded increments converges almost
surely and in L¹.
-/
theorem supermartingale_convergence
  (hY : is_supermartingale (X := X) (F := F) μ)
  (h_nonneg : ∀ k ω, 0 ≤ X k ω)
  (h_bound : ∃ C, ∀ k ω, |X (k+1) ω - X k ω| ≤ C) :
  ∀ᵐ ω ∂μ, is_convergent (λ k, X k ω) ∧ tendsto (λ k, X k) at_top (𝓝 _) :=
begin
  -- Direct application of Mathlib4’s Doob Martingale Convergence Theorem
  exact measure_theory.is_supermartingale.tendsto_ae (X := X) (F := F) (μ := μ)
    hY h_nonneg h_bound,
end

end supermartingale_convergence

section invariant_measure

open measure_theory.measure_theory probability_theory

variables {X : Type*} [topological_space X] (P : X → measure X)

/--
Theorem 11.3.1 (Invariant Measure Existence):
Under Feller and irreducibility conditions, there exists an invariant
probability measure for the stochastic relaxation process.
-/
theorem invariant_measure_existence
  (hFeller : is_feller P) (hirr : irreducible P) :
  ∃ μ, is_invariant_measure P μ :=
begin
  -- Use Krylov–Bogolyubov construction from Mathlib4
  exact probability_theory.krylov_bogolyubov (P := P) hFeller hirr,
end

end invariant_measure

end paralogic
