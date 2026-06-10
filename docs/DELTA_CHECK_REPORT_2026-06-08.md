# Delta Check Report - 2026-06-08

Status: DLC-pass.

Scope: bounded executable check over the two finite Delta systems currently
mirrored in Lean:

- `twoDeltaSystem`
- `loopDeltaSystem`

The checker computes reachability, stable states, eventual resolution, global
finality, eventual stability, and eventual stable resolution.  It then verifies
that named Lean theorem witnesses are supported by the executable records.  It
also records finite closure candidates for the two-state Delta system.
Finally, it exhaustively sweeps all two-state systems with initial state `a`,
all directed step relations, and outcomes in `{iterative, resolution}`.
It also exhaustively sweeps the corresponding three-state universe.

Artifacts:

- `python/delta_check.py`
- `src/Paralogic/DeltaDynamics.lean`
- `docs/delta_checks/coverage.json`
- `docs/delta_checks/closure_records.json`
- `docs/delta_checks/lean_named_witnesses.json`
- `docs/delta_checks/summary.json`
- `docs/delta_checks/two_state_sweep.json`
- `docs/delta_checks/two_state_sweep_summary.json`
- `docs/delta_checks/three_state_sweep.json`
- `docs/delta_checks/three_state_sweep_summary.json`

Results:

- finite systems checked: 2
- closure records checked: 3
- exhaustive two-state systems swept: 64
- exhaustive three-state systems swept: 4096
- Lean-named witnesses checked: 6
- missing Lean-named witnesses: 0
- two-state reachable-closure failures: 0
- two-state always-implies-eventually failures: 0
- two-state eventual-resolution-not-global-finality witnesses: 16
- two-state eventual-stability-not-eventual-resolution witnesses: 20
- two-state stable-resolution-not-global-finality witnesses: 4
- three-state reachable-closure failures: 0
- three-state always-implies-eventually failures: 0
- three-state eventual-resolution-not-global-finality witnesses: 2048
- three-state eventual-stability-not-eventual-resolution witnesses: 728
- three-state stable-resolution-not-global-finality witnesses: 408

Claim warranted by this checker:

- The executable records support the named Lean witnesses for:
  `eventual_resolution_not_global_finality`,
  `stable_resolution_not_global_finality`, and
  `eventual_stability_not_eventual_resolution`.
- The executable closure records support the named Lean witnesses for:
  `twoDelta_all_states_closed`, `twoDelta_start_only_not_closed`, and
  `delta_reachable_closed`.
- The Lean layer additionally contains modal reachable-state operators
  `DeltaAlways` and `DeltaEventually`; those modal theorems are checked by
  `lake build`, not by this bounded executable checker.
- The Lean layer additionally proves the least-closure theorem
  `delta_reachable_least_closed`; the executable checker records concrete
  finite closure cases, not the general theorem.
- In the exhaustive two-state sweep, every generated reachable set is closed
  and every generated global-finality case has eventual resolution.
- The same two invariants also hold over the exhaustive three-state sweep.

Claim explicitly not warranted by this checker:

- This is not a general model checker for all finite Delta systems; the sweep
  is exhaustive only for the declared two-state and three-state universes.
- This does not prove coalgebraic modal completeness.
- This does not decide empirical truth, repair closure, or source-backed ISFT
  mechanism semantics.
