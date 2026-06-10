import Paralogic.InsightDelta

/-!
Finite Delta dynamics.

This module begins the coalgebraic/dynamic lane in a concrete way: a Delta
system is a transition structure with an outcome assigned to each state.
Reachability is inductive, stable states are defined, and a finite loop gives
a checked counterexample to the overclaim that every Delta process eventually
reaches resolution.
-/

namespace Paralogic

structure DeltaTransitionSystem : Type 1 where
  State : Type
  initial : State
  step : State -> State -> Prop
  outcome : State -> DeltaOutcome

inductive DeltaReachable (system : DeltaTransitionSystem) :
    system.State -> Prop where
  | initial : DeltaReachable system system.initial
  | step {source target : system.State} :
      DeltaReachable system source ->
      system.step source target ->
      DeltaReachable system target

def DeltaClosed (system : DeltaTransitionSystem)
    (candidate : system.State -> Prop) : Prop :=
  And (candidate system.initial)
    (forall source target : system.State,
      candidate source -> system.step source target -> candidate target)

theorem delta_reachable_closed
    (system : DeltaTransitionSystem) :
    DeltaClosed system (DeltaReachable system) :=
  And.intro DeltaReachable.initial
    (fun _ _ hReach hStep => DeltaReachable.step hReach hStep)

theorem delta_reachable_least_closed
    (system : DeltaTransitionSystem)
    (candidate : system.State -> Prop)
    (hClosed : DeltaClosed system candidate)
    {state : system.State}
    (hReach : DeltaReachable system state) :
    candidate state := by
  induction hReach with
  | initial =>
      exact hClosed.left
  | step hReach hStep ih =>
      exact hClosed.right _ _ ih hStep

def DeltaStable (system : DeltaTransitionSystem)
    (state : system.State) : Prop :=
  forall target : system.State, system.step state target -> target = state

def EventuallyResolution (system : DeltaTransitionSystem) : Prop :=
  Exists (fun state : system.State =>
    And (DeltaReachable system state)
      (system.outcome state = DeltaOutcome.resolution))

def DeltaGlobalFinality (system : DeltaTransitionSystem) : Prop :=
  forall state : system.State,
    DeltaReachable system state ->
    system.outcome state = DeltaOutcome.resolution

def EventuallyStable (system : DeltaTransitionSystem) : Prop :=
  Exists (fun state : system.State =>
    And (DeltaReachable system state)
      (DeltaStable system state))

def EventuallyStableResolution (system : DeltaTransitionSystem) : Prop :=
  Exists (fun state : system.State =>
    And (DeltaReachable system state)
      (And (system.outcome state = DeltaOutcome.resolution)
        (DeltaStable system state)))

def DeltaAlways (system : DeltaTransitionSystem)
    (property : system.State -> Prop) : Prop :=
  forall state : system.State, DeltaReachable system state -> property state

def DeltaEventually (system : DeltaTransitionSystem)
    (property : system.State -> Prop) : Prop :=
  Exists (fun state : system.State =>
    And (DeltaReachable system state) (property state))

def IsResolutionState (system : DeltaTransitionSystem)
    (state : system.State) : Prop :=
  system.outcome state = DeltaOutcome.resolution

def IsStableState (system : DeltaTransitionSystem)
    (state : system.State) : Prop :=
  DeltaStable system state

theorem delta_always_implies_eventually
    (system : DeltaTransitionSystem)
    (property : system.State -> Prop)
    (hAlways : DeltaAlways system property) :
    DeltaEventually system property :=
  Exists.intro system.initial
    (And.intro DeltaReachable.initial
      (hAlways system.initial DeltaReachable.initial))

theorem eventual_resolution_iff_eventually_resolution_state
    (system : DeltaTransitionSystem) :
    Iff (EventuallyResolution system)
      (DeltaEventually system (IsResolutionState system)) :=
  Iff.rfl

theorem global_finality_iff_always_resolution
    (system : DeltaTransitionSystem) :
    Iff (DeltaGlobalFinality system)
      (DeltaAlways system (IsResolutionState system)) :=
  Iff.rfl

theorem stable_resolution_implies_eventual_resolution
    (system : DeltaTransitionSystem)
    (h : EventuallyStableResolution system) :
    EventuallyResolution system := by
  cases h with
  | intro state hState =>
      exact Exists.intro state (And.intro hState.left hState.right.left)

theorem delta_step_preserves_reachability
    (system : DeltaTransitionSystem)
    {source target : system.State}
    (hReach : DeltaReachable system source)
    (hStep : system.step source target) :
    DeltaReachable system target :=
  DeltaReachable.step hReach hStep

theorem stable_blocks_nonself_step
    (system : DeltaTransitionSystem)
    {source target : system.State}
    (hStable : DeltaStable system source)
    (hNe : Not (target = source)) :
    Not (system.step source target) := by
  intro hStep
  exact hNe (hStable target hStep)

inductive TwoDeltaState where
  | start
  | repaired
  deriving DecidableEq, Repr

def twoDeltaStep : TwoDeltaState -> TwoDeltaState -> Prop
  | TwoDeltaState.start, TwoDeltaState.repaired => True
  | _, _ => False

def twoDeltaOutcome : TwoDeltaState -> DeltaOutcome
  | TwoDeltaState.start => DeltaOutcome.iterative
  | TwoDeltaState.repaired => DeltaOutcome.resolution

def twoDeltaSystem : DeltaTransitionSystem :=
  { State := TwoDeltaState
    initial := TwoDeltaState.start
    step := twoDeltaStep
    outcome := twoDeltaOutcome }

def twoDeltaAllStates (_state : TwoDeltaState) : Prop := True

def twoDeltaStartOnly : TwoDeltaState -> Prop
  | TwoDeltaState.start => True
  | TwoDeltaState.repaired => False

theorem twoDelta_all_states_closed :
    DeltaClosed twoDeltaSystem twoDeltaAllStates :=
  And.intro True.intro
    (fun _ _ _ _ => True.intro)

theorem twoDelta_start_only_not_closed :
    Not (DeltaClosed twoDeltaSystem twoDeltaStartOnly) := by
  intro hClosed
  exact hClosed.right TwoDeltaState.start TwoDeltaState.repaired
    True.intro True.intro

theorem twoDelta_repaired_in_every_closed
    (candidate : TwoDeltaState -> Prop)
    (hClosed : DeltaClosed twoDeltaSystem candidate) :
    candidate TwoDeltaState.repaired :=
  delta_reachable_least_closed twoDeltaSystem candidate hClosed
    (DeltaReachable.step DeltaReachable.initial True.intro)

theorem twoDelta_repaired_reachable :
    DeltaReachable twoDeltaSystem TwoDeltaState.repaired :=
  DeltaReachable.step DeltaReachable.initial True.intro

theorem twoDelta_eventually_resolution :
    EventuallyResolution twoDeltaSystem :=
  Exists.intro TwoDeltaState.repaired
    (And.intro twoDelta_repaired_reachable rfl)

theorem twoDelta_start_reachable :
    DeltaReachable twoDeltaSystem TwoDeltaState.start :=
  DeltaReachable.initial

theorem twoDelta_not_global_finality :
    Not (DeltaGlobalFinality twoDeltaSystem) := by
  intro hFinal
  have hResolution :
      twoDeltaSystem.outcome TwoDeltaState.start =
        DeltaOutcome.resolution :=
    hFinal TwoDeltaState.start twoDelta_start_reachable
  cases hResolution

theorem eventual_resolution_not_global_finality :
    And (EventuallyResolution twoDeltaSystem)
      (Not (DeltaGlobalFinality twoDeltaSystem)) :=
  And.intro twoDelta_eventually_resolution twoDelta_not_global_finality

theorem twoDelta_eventually_resolution_modal :
    DeltaEventually twoDeltaSystem (IsResolutionState twoDeltaSystem) :=
  (eventual_resolution_iff_eventually_resolution_state twoDeltaSystem).mp
    twoDelta_eventually_resolution

theorem twoDelta_not_always_resolution_modal :
    Not (DeltaAlways twoDeltaSystem (IsResolutionState twoDeltaSystem)) :=
  (fun hAlways =>
    twoDelta_not_global_finality
      ((global_finality_iff_always_resolution twoDeltaSystem).mpr hAlways))

theorem eventual_not_always_resolution_modal :
    And
      (DeltaEventually twoDeltaSystem (IsResolutionState twoDeltaSystem))
      (Not (DeltaAlways twoDeltaSystem
        (IsResolutionState twoDeltaSystem))) :=
  And.intro twoDelta_eventually_resolution_modal
    twoDelta_not_always_resolution_modal

theorem twoDelta_repaired_stable :
    DeltaStable twoDeltaSystem TwoDeltaState.repaired := by
  intro target hStep
  cases target <;> cases hStep

theorem twoDelta_eventually_stable :
    EventuallyStable twoDeltaSystem :=
  Exists.intro TwoDeltaState.repaired
    (And.intro twoDelta_repaired_reachable twoDelta_repaired_stable)

theorem twoDelta_eventually_stable_resolution :
    EventuallyStableResolution twoDeltaSystem :=
  Exists.intro TwoDeltaState.repaired
    (And.intro twoDelta_repaired_reachable
      (And.intro rfl twoDelta_repaired_stable))

theorem stable_resolution_not_global_finality :
    And (EventuallyStableResolution twoDeltaSystem)
      (Not (DeltaGlobalFinality twoDeltaSystem)) :=
  And.intro twoDelta_eventually_stable_resolution
    twoDelta_not_global_finality

theorem twoDelta_start_not_stable :
    Not (DeltaStable twoDeltaSystem TwoDeltaState.start) := by
  intro hStable
  have hEq :
      TwoDeltaState.repaired = TwoDeltaState.start :=
    hStable TwoDeltaState.repaired True.intro
  cases hEq

inductive LoopDeltaState where
  | loop
  deriving DecidableEq, Repr

def loopDeltaStep : LoopDeltaState -> LoopDeltaState -> Prop
  | LoopDeltaState.loop, LoopDeltaState.loop => True

def loopDeltaOutcome (_state : LoopDeltaState) : DeltaOutcome :=
  DeltaOutcome.iterative

def loopDeltaSystem : DeltaTransitionSystem :=
  { State := LoopDeltaState
    initial := LoopDeltaState.loop
    step := loopDeltaStep
    outcome := loopDeltaOutcome }

theorem loopDelta_reachable :
    DeltaReachable loopDeltaSystem LoopDeltaState.loop :=
  DeltaReachable.initial

theorem loopDelta_stable :
    DeltaStable loopDeltaSystem LoopDeltaState.loop := by
  intro target hStep
  cases target
  rfl

theorem loopDelta_eventually_stable :
    EventuallyStable loopDeltaSystem :=
  Exists.intro LoopDeltaState.loop
    (And.intro loopDelta_reachable loopDelta_stable)

theorem loopDelta_not_eventually_resolution :
    Not (EventuallyResolution loopDeltaSystem) := by
  intro h
  cases h with
  | intro state hState =>
      cases state
      cases hState.right

theorem eventual_stability_not_eventual_resolution :
    And (EventuallyStable loopDeltaSystem)
      (Not (EventuallyResolution loopDeltaSystem)) :=
  And.intro loopDelta_eventually_stable
    loopDelta_not_eventually_resolution

theorem loopDelta_eventually_stable_modal :
    DeltaEventually loopDeltaSystem (IsStableState loopDeltaSystem) :=
  loopDelta_eventually_stable

theorem loopDelta_not_eventually_resolution_modal :
    Not (DeltaEventually loopDeltaSystem
      (IsResolutionState loopDeltaSystem)) := by
  intro hEventually
  exact loopDelta_not_eventually_resolution
    ((eventual_resolution_iff_eventually_resolution_state loopDeltaSystem).mpr
      hEventually)

theorem eventual_stability_not_eventual_resolution_modal :
    And
      (DeltaEventually loopDeltaSystem (IsStableState loopDeltaSystem))
      (Not (DeltaEventually loopDeltaSystem
        (IsResolutionState loopDeltaSystem))) :=
  And.intro loopDelta_eventually_stable_modal
    loopDelta_not_eventually_resolution_modal

end Paralogic
