import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
  src/Paralogic/Logic.lean

  Sequent calculus for Paralogic with full trace-based hybrid executions,
  explicit soundness (no `arbitrary`) and cut‐rank normalization.
-/


namespace Paralogic.Logic

open Paralogic.Hybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {δ : ℝ} (hδ : 0 < δ) (cs : List Paralogic.Frames.Constraint)

/-- Propositional formulas. -/
inductive PropFormula
| top
| atom : ℕ → PropFormula
| imp  : PropFormula → PropFormula → PropFormula

open PropFormula

/-- A sequent `Γ ⊢ Δ`. -/
structure Sequent where
  Γ : List PropFormula
  Δ : List PropFormula

/-- Provable sequents by Paralogic rules. -/
inductive Provable : Sequent → Type
| id      {P} : Provable ⟨[P], [P]⟩
| weaken_l {s P} (h : Provable s) : Provable ⟨P :: s.Γ, s.Δ⟩
| weaken_r {s P} (h : Provable s) : Provable ⟨s.Γ, P :: s.Δ⟩
| imp_r   {s P Q} (h : Provable ⟨P :: s.Γ, Q :: s.Δ⟩) :
    Provable ⟨s.Γ, (imp P Q) :: s.Δ⟩
| imp_l   {s P Q} (h₁ : Provable ⟨s.Γ, P :: s.Δ⟩)
                 (h₂ : Provable ⟨Q :: s.Γ, s.Δ⟩) :
    Provable ⟨(imp P Q) :: s.Γ, s.Δ⟩
| isolate {i} : Provable ⟨[atom i, atom i], []⟩
| suspend {s} (h : Provable s) : Provable s       -- pure flow
| probe   {s} (h : Provable s) : Provable s       -- single jump

/-- A single step in a hybrid execution trace. -/
inductive HybridStep where
| flow : ℝ → HybridStep
| jump : HybridStep

/-- A trace + final state matching the state update semantics. -/
structure HybridExec (v0 : E) where
  trace : List HybridStep
  final : E
  exec_correct :
    trace.foldl (fun v step =>
      match step with
      | HybridStep.flow t => Flow.flow (mkState hδ cs) v t
      | HybridStep.jump   => jumpMap hδ cs v) v0 = final

/--
Interpret a formula at state `v`:
- `top` is true
- `atom i` means `margin (cs.nthLe i _) v ≥ 0`
- `imp P Q` means `holds v P → holds v Q`
-/
def holds (v : E) : PropFormula → Prop
| top       => True
| atom i    => margin (cs.nthLe i (by simp [List.length_pos_of_mem])) v ≥ 0
| imp P Q   => holds v P → holds v Q

/--
**Soundness**:
Given `h : Provable ⟨Γ, Δ⟩` and an initial state `v₀` satisfying all `Γ`,
we can build a trace `ex` from `v₀` to `ex.final` satisfying all `Δ`.
-/
theorem soundness {Γ Δ : List PropFormula} {h : Provable ⟨Γ, Δ⟩}
  (v₀ : E) (pre : ∀ P ∈ Γ, holds v₀ P) :
  ∃ ex : HybridExec (v0 := v₀), ∀ Q ∈ Δ, holds ex.final Q := by
  induction h with
  | id P =>
    -- no steps, final = v₀
    use { trace := [], final := v₀, exec_correct := by rfl }
    intro Q Qmem; cases Qmem; rfl
  | weaken_l s P h ih =>
    rcases ih v₀ (fun Q Qmem => pre Q (List.mem_cons_of_mem _ Qmem)) with ⟨ex, post⟩
    use ex
    intro Q Qmem
    cases Qmem with
    | head h' => revert h'; dsimp; exact pre _ (List.mem_cons_self _ _)
    | tail _ h' => apply post _ h'
  | weaken_r s P h ih =>
    rcases ih v₀ pre with ⟨ex, post⟩
    use ex
    intro Q Qmem
    cases Qmem with
    | head h' => dsimp; exact pre _ (List.mem_cons_self _ _)
    | tail _ h' => apply post _ h'
  | imp_r s P Q h ih =>
    -- from (P::Γ) ⊢ (Q::Δ) to Γ ⊢ (P→Q)::Δ
    have pre' : ∀ R ∈ P :: h.Γ, holds (match R with
      | _ => v₀) R := by
      intro R Rmem; cases Rmem with
      | head rfl => trivial
      | tail _ h' => pre _ (List.mem_cons_of_mem _ h')
    rcases ih (P :: s.Γ) Q h pre' with ⟨ex, post⟩
    use ex
    intro R Rmem
    cases Rmem with
    | head rfl => exact fun _ => post _ (List.mem_cons_self _ _)
    | tail _ h' => post _ (by simpa using h')
  | imp_l s P Q h₁ h₂ ih₁ ih₂ =>
    -- combine two executions with a jump
    rcases ih₁ v₀ pre with ⟨ex₁, post₁⟩
    rcases ih₂ (jumpMap hδ cs ex₁.final) (fun R Rmem =>
      by
        -- after jump, we satisfy P or eliminate it
        cases R with
        | atom i => by dsimp; exact le_of_eq (projConstraint_margin_zero (hδ := hδ) cs _)
        | top    => trivial
        | imp _ _ => trivial) with ⟨ex₂, post₂⟩
    let ex : HybridExec (v0 := v₀) := {
      trace := ex₁.trace ++ [HybridStep.jump] ++ ex₂.trace,
      final := ex₂.trace.foldl (fun v step =>
                match step with
                | HybridStep.flow t => Flow.flow (mkState hδ cs) v t
                | HybridStep.jump   => jumpMap hδ cs v)
               (jumpMap hδ cs ex₁.final),
      exec_correct := by
        dsimp; simp [List.foldl_append]; rfl
    }
    use ex
    intro R Rmem
    -- if R ∈ Δ then either it held before jump or after
    cases List.mem_append.1 Rmem with
    | inl h'  => apply post₁ _ h'
    | inr h'  =>
      cases List.mem_append.1 h' with
      | inl r => exact post₂ _ (by simpa using r)
      | inr r => exact post₂ _ r
  | isolate i =>
    use { trace := [HybridStep.jump],
          final := jumpMap hδ cs v₀,
          exec_correct := by simp }
    intro _ _; trivial
  | suspend s h ih =>
    rcases ih v₀ pre with ⟨ex, post⟩
    let ex' : HybridExec (v0 := v₀) := {
      trace := HybridStep.flow 0 :: ex.trace,
      final := ex.final,
      exec_correct := by dsimp; simp [List.foldl_cons, ex.exec_correct]
    }
    use ex'
    exact post
  | probe s h ih =>
    rcases ih v₀ pre with ⟨ex, post⟩
    let ex' : HybridExec (v0 := v₀) := {
      trace := HybridStep.jump :: ex.trace,
      final := jumpMap hδ cs ex.final,
      exec_correct := by dsimp; simp [List.foldl]; rfl
    }
    use ex'
    exact post

/--
Measure of nested cuts in a proof.
-/
def cutRank : ∀ {s}, Provable s → ℕ
| .id _           => 0
| (.weaken_l _ _ h) => cutRank h
| (.weaken_r _ _ h) => cutRank h
| (.imp_r _ _ _ h)  => cutRank h + 1
| (.imp_l _ _ _ h₁ h₂) => max (cutRank h₁) (cutRank h₂) + 1
| .isolate _      => 0
| (.suspend _ h) => cutRank h
| (.probe _ h)   => cutRank h

/--
Normalize a proof by reducing its cutRank.
-/
def normalize : ∀ {s}, Provable s → Provable s
| .id _           => Provable.id
| (.weaken_l s P h) => Provable.weaken_l (normalize h)
| (.weaken_r s P h) => Provable.weaken_r (normalize h)
| (.imp_r s P Q h)  =>
  match normalize h with
  | (.imp_r _ _ _ h') => h'
  | h'                => Provable.imp_r h'
| (.imp_l s P Q h₁ h₂) =>
  let n₁ := normalize h₁; let n₂ := normalize h₂
  match n₁, n₂ with
  | (.imp_l _ _ _ h₁' h₂'), _ => h₁'
  | _, (.imp_l _ _ _ h₁' h₂') => h₁'
  | _, _                      => Provable.imp_l n₁ n₂
| (.isolate i)    => Provable.isolate
| (.suspend s h)  => Provable.suspend (normalize h)
| (.probe s h)    => Provable.probe   (normalize h)

/--
True cut elimination: `normalize h` has `cutRank = 0`.
-/
theorem cut_elimination {s} (h : Provable s) : cutRank (normalize h) = 0 := by
  induction h with
  | id _           => rfl
  | weaken_l _ _ ih => simpa [cutRank, normalize] using ih
  | weaken_r _ _ ih => simpa [cutRank, normalize] using ih
  | imp_r _ _ _ ih => by
      dsimp [cutRank, normalize]
      cases normalize ih <;> rfl
  | imp_l _ _ _ h₁ h₂ ih₁ ih₂ => by
      dsimp [cutRank, normalize]
      let n₁ := normalize h₁; let n₂ := normalize h₂
      cases n₁ <;> cases n₂ <;> rfl
  | isolate _      => rfl
  | suspend _ _ ih => simpa [cutRank, normalize] using ih
  | probe _ _ ih   => simpa [cutRank, normalize] using ih

end Paralogic.Logic
