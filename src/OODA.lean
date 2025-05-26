import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
  src/Paralogic/OODA.lean

  Integration of OODA loops and kill‐chain phases into Paralogic.
  Defines the OODA cycle, kill‐chain structure, system state,
  actions, transitions, reachability, and a detailed chain‐collapse
  theorem: if you inject a fresh paradox P into an initially empty
  pending list, then any subsequent kill‐chain completion must first
  resolve that very paradox.
-/

namespace Paralogic.OODA

open Mathlib.Data.Finset
open Mathlib.Data.List
open Paralogic.Logic

/-- The four stages of the OODA loop. -/
inductive Stage
| Observe
| Orient
| Decide
| Act
deriving DecidableEq, Repr

/-- Advance to the next OODA stage. -/
def nextStage : Stage → Stage
| Stage.Observe => Stage.Orient
| Stage.Orient  => Stage.Decide
| Stage.Decide  => Stage.Act
| Stage.Act     => Stage.Observe

/-- Standard phases of the cyber kill-chain. -/
inductive KillPhase
| Reconnaissance
| Weaponization
| Delivery
| Exploitation
| Installation
| CommandAndControl
| Actions
deriving DecidableEq, Repr

/--
A `State` bundles:
• `stage`   : current OODA stage,
• `phases`  : completed kill-chain phases,
• `pending` : list of unresolved paradox probes.
-/
structure State where
  stage   : Stage
  phases  : Finset KillPhase
  pending : List PropFormula
deriving Repr

/-- Actions driving state transitions. -/
inductive Action
| toStage
| phaseComplete (kp : KillPhase)
| paradoxProbe  (P  : PropFormula)
| resolveProbe
deriving DecidableEq, Repr

/--
One-step transition `s --a→ s'`:
- `toStage` only if no pending probes,
- `phaseComplete kp` only when `stage = Act` and no pending probes,
- `paradoxProbe P` always appends `P` to `pending`,
- `resolveProbe` pops the head of `pending`.
-/
inductive Transition : State → Action → State → Prop
| step_stage {s s'} (hp : s.pending = [])
    (h₁ : s'.stage  = nextStage s.stage)
    (h₂ : s'.phases = s.phases)
    (h₃ : s'.pending = []) :
    Transition s Action.toStage s'
| complete_phase {s s'} {kp : KillPhase}
    (hstage : s.stage = Stage.Act)
    (hp    : s.pending = [])
    (h₁    : s'.phases = s.phases.insert kp)
    (h₂    : s'.stage  = Stage.Observe)
    (h₃    : s'.pending = []) :
    Transition s (Action.phaseComplete kp) s'
| inject_paradox {s s'} {P : PropFormula}
    (h₁ : s'.stage   = s.stage)
    (h₂ : s'.phases  = s.phases)
    (h₃ : s'.pending = s.pending ++ [P]) :
    Transition s (Action.paradoxProbe P) s'
| resolve_paradox {s s'} {P : PropFormula} {rest : List PropFormula}
    (h₁ : s.pending = P :: rest)
    (h₂ : s'.stage   = s.stage)
    (h₃ : s'.phases  = s.phases)
    (h₄ : s'.pending = rest) :
    Transition s Action.resolveProbe s'
deriving Repr

/--
A **trace** of transitions from `s₀` to `sₙ`, carrying each `(Action × State)`.
-/
inductive Reachable : State → List (Action × State) → State → Prop
| nil  {s} : Reachable s [] s
| cons {s₀ s₁ s₂ : State} {a : Action} {rest : List (Action × State)}
    (h : Transition s₀ a s₁)
    (ht : Reachable s₁ rest s₂) :
    Reachable s₀ ((a, s₁) :: rest) s₂

/--
**Chain-collapse theorem**: Let `s` be any state with
no pending probes (`s.pending = []`).  Inject a fresh paradox `P`:

```lean
let s' := { s with pending := [P] }
```

Then in any reachable trace from `s'` whose last action is
`phaseComplete kp`, there must be a preceding `resolveProbe`
that removes exactly `P` (since it was the sole pending item).
-/
theorem chainCollapse
  {s : State} {P : PropFormula} {kp : KillPhase}
  (h0 : s.pending = [])
  {trace s_end}
  (hR : Reachable ({ s with pending := [P] }) trace s_end)
  (hLast : trace.last? = some (Action.phaseComplete kp, s_end)) :
  ∃ pre mid post,
    trace = pre ++ (Action.resolveProbe, mid) :: post ∧
    mid.pending = [] := by
  induction hR with
  | nil =>
    -- No steps, cannot end with `phaseComplete`
    cases hLast
  | cons s₀ s₁ s₂ a rest hStep hRec ih =>
    -- Head of trace is `(a, s₁)`
    cases a
    case resolveProbe =>
      -- Since `s₀.pending = [P]`, `s₁.pending = []`, so this resolves P
      use [], s₁, rest
      simp [hRec]
      rfl
    case paradoxProbe P' =>
      -- Injection does not resolve; recurse on the tail
      have hTailLast : rest.last? = some (Action.phaseComplete kp, s₂) := by
        simpa using hLast
      rcases ih hRec hTailLast with ⟨pre, mid, post, heq, hmid⟩
      use (Action.paradoxProbe P', s₁) :: pre, mid, post
      simp [heq]
    case toStage =>
      -- `toStage` requires no pending probes, but `s₀.pending = [P] ≠ []`
      dsimp at hStep; cases hStep
    case phaseComplete kp' =>
      -- Direct `phaseComplete` at head impossible: pending ≠ []
      dsimp at hStep; cases hStep

end Paralogic.OODA
