import Mathlib.Data.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

-/!
  src/Paralogic/MultiAgent.lean

  Game-theoretic definitions: games, Nash equilibria, social cost, and Price of Anarchy.
-/


namespace Paralogic.MultiAgent

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/--
A finite game with player set `P`, each player `p` has a finite strategy set `S p`,
and a nonnegative cost function `cost p : Profile → ℝ` depending on the full profile.
-/
structure Game where
  S        : P → Type*
  [strat_fintype : ∀ p, Fintype (S p)]
  [strat_dec : ∀ p, DecidableEq (S p)]
  cost     : (p : P) → (Profile : Π p, S p) → ℝ
  cost_nonneg : ∀ p (σ : Π p, S p), 0 ≤ cost p σ

attribute [instance] Game.strat_fintype Game.strat_dec

/--
A strategy profile is a choice of strategy for each player.
-/
instance Profile : Type* := Π p, Game.S _

/--
The social cost is the sum of individual costs.
-/
def socialCost (G : Game) (σ : Π p, G.S p) : ℝ :=
  (∑ p, G.cost p σ)

/--
A Nash equilibrium is a profile where no player can unilaterally
decrease their cost by deviating.
-/
def isNash (G : Game) (σ : Π p, G.S p) : Prop :=
  ∀ p s, G.cost p σ ≤ G.cost p (Function.update σ p s)

/--
An optimal profile minimizes social cost.
-/
def isOptimal (G : Game) (σ : Π p, G.S p) : Prop :=
  ∀ τ, socialCost G σ ≤ socialCost G τ

/--
The Price of Anarchy ratio for a Nash equilibrium `σ` and optimum `σ*`.
Requires `σ` is Nash and `σ*` is optimal and nonzero social cost.
-/
def PoA_ratio (G : Game) (σ σ* : Π p, G.S p)
  (hN : isNash G σ) (hO : isOptimal G σ*) (hpos : 0 < socialCost G σ*) : ℝ :=
  socialCost G σ / socialCost G σ*

/--
Trivial bound: any equilibrium has social cost at least optimum,
so PoA_ratio ≥ 1.
-/
theorem PoA_ratio_ge_one (G : Game) {σ σ*}
  (hN : isNash G σ) (hO : isOptimal G σ*) (hpos : 0 < socialCost G σ*) :
  1 ≤ PoA_ratio G σ σ* hN hO hpos := by
  dsimp [PoA_ratio]
  have h_opt_le : socialCost G σ* ≤ socialCost G σ := by
    apply hO
  have h_div : 1 = socialCost G σ* / socialCost G σ* := by
    field_simp [hpos.ne']
  calc
    1 = socialCost G σ*/socialCost G σ* := h_div.symm
    _ ≤ socialCost G σ / socialCost G σ* := by
      apply div_le_div_of_le (n := _) (m := _)
        (by linarith [G.cost_nonneg _ σ]) h_opt_le hpos
      all_goals apply le_of_lt <;> linarith [hpos]
end Paralogic.MultiAgent
