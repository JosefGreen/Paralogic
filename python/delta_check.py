from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from pathlib import Path


State = str
Outcome = str
Step = tuple[State, State]
Candidate = frozenset[State]

RESOLUTION = "resolution"
ITERATIVE = "iterative"


@dataclass(frozen=True)
class DeltaSystem:
    id: str
    states: tuple[State, ...]
    initial: State
    steps: frozenset[Step]
    outcomes: dict[State, Outcome]


TWO_DELTA = DeltaSystem(
    id="twoDeltaSystem",
    states=("start", "repaired"),
    initial="start",
    steps=frozenset({("start", "repaired")}),
    outcomes={"start": ITERATIVE, "repaired": RESOLUTION},
)

LOOP_DELTA = DeltaSystem(
    id="loopDeltaSystem",
    states=("loop",),
    initial="loop",
    steps=frozenset({("loop", "loop")}),
    outcomes={"loop": ITERATIVE},
)

SYSTEMS: tuple[DeltaSystem, ...] = (TWO_DELTA, LOOP_DELTA)


def reachable(system: DeltaSystem) -> set[State]:
    reached = {system.initial}
    changed = True
    while changed:
        changed = False
        for source, target in system.steps:
            if source in reached and target not in reached:
                reached.add(target)
                changed = True
    return reached


def stable(system: DeltaSystem, state: State) -> bool:
    return all(target == state for source, target in system.steps if source == state)


def closed(system: DeltaSystem, candidate: Candidate) -> bool:
    contains_initial = system.initial in candidate
    closed_under_step = all(
        target in candidate
        for source, target in system.steps
        if source in candidate
    )
    return contains_initial and closed_under_step


def eventually_resolution(system: DeltaSystem) -> bool:
    return any(
        system.outcomes[state] == RESOLUTION
        for state in reachable(system)
    )


def global_finality(system: DeltaSystem) -> bool:
    return all(
        system.outcomes[state] == RESOLUTION
        for state in reachable(system)
    )


def eventually_stable(system: DeltaSystem) -> bool:
    return any(stable(system, state) for state in reachable(system))


def eventually_stable_resolution(system: DeltaSystem) -> bool:
    return any(
        system.outcomes[state] == RESOLUTION and stable(system, state)
        for state in reachable(system)
    )


def system_record(system: DeltaSystem) -> dict[str, object]:
    reached = sorted(reachable(system))
    return {
        "id": system.id,
        "states": list(system.states),
        "initial": system.initial,
        "steps": [[source, target] for source, target in sorted(system.steps)],
        "reachable": reached,
        "outcomes": dict(sorted(system.outcomes.items())),
        "stable_states": [
            state for state in reached if stable(system, state)
        ],
        "eventually_resolution": eventually_resolution(system),
        "global_finality": global_finality(system),
        "eventually_stable": eventually_stable(system),
        "eventually_stable_resolution": eventually_stable_resolution(system),
    }


def coverage() -> list[dict[str, object]]:
    return [system_record(system) for system in SYSTEMS]


def candidate_payload(candidate: Candidate) -> list[State]:
    return sorted(candidate)


def closure_records() -> list[dict[str, object]]:
    two_delta_reachable = frozenset(reachable(TWO_DELTA))
    rows = [
        {
            "id": "twoDeltaAllStates",
            "system": TWO_DELTA.id,
            "candidate": candidate_payload(frozenset(TWO_DELTA.states)),
            "closed": closed(TWO_DELTA, frozenset(TWO_DELTA.states)),
        },
        {
            "id": "twoDeltaStartOnly",
            "system": TWO_DELTA.id,
            "candidate": candidate_payload(frozenset({"start"})),
            "closed": closed(TWO_DELTA, frozenset({"start"})),
        },
        {
            "id": "twoDeltaReachable",
            "system": TWO_DELTA.id,
            "candidate": candidate_payload(two_delta_reachable),
            "closed": closed(TWO_DELTA, two_delta_reachable),
        },
    ]
    return rows


def bounded_state_systems(
    states: tuple[State, ...],
    id_prefix: str,
) -> list[DeltaSystem]:
    possible_steps = tuple((source, target) for source in states for target in states)
    systems = []
    for step_mask in itertools.product([False, True], repeat=len(possible_steps)):
        steps = frozenset(
            step
            for include, step in zip(step_mask, possible_steps)
            if include
        )
        for outcome_bits in itertools.product([ITERATIVE, RESOLUTION], repeat=len(states)):
            outcomes = {state: outcome for state, outcome in zip(states, outcome_bits)}
            step_code = "".join("1" if bit else "0" for bit in step_mask)
            outcome_code = "".join("R" if outcome == RESOLUTION else "I" for outcome in outcome_bits)
            systems.append(
                DeltaSystem(
                    id=f"{id_prefix}-{step_code}-{outcome_code}",
                    states=states,
                    initial=states[0],
                    steps=steps,
                    outcomes=outcomes,
                )
            )
    return systems


def all_two_state_systems() -> list[DeltaSystem]:
    return bounded_state_systems(("a", "b"), "twoState")


def all_three_state_systems() -> list[DeltaSystem]:
    return bounded_state_systems(("a", "b", "c"), "threeState")


def sweep_record(system: DeltaSystem) -> dict[str, object]:
    record = system_record(system)
    reachable_candidate = frozenset(reachable(system))
    record["reachable_closed"] = closed(system, reachable_candidate)
    record["eventual_resolution_not_global_finality"] = (
        record["eventually_resolution"] and not record["global_finality"]
    )
    record["eventual_stability_not_eventual_resolution"] = (
        record["eventually_stable"] and not record["eventually_resolution"]
    )
    record["stable_resolution_not_global_finality"] = (
        record["eventually_stable_resolution"] and not record["global_finality"]
    )
    return record


def two_state_sweep_records() -> list[dict[str, object]]:
    return [sweep_record(system) for system in all_two_state_systems()]


def three_state_sweep_records() -> list[dict[str, object]]:
    return [sweep_record(system) for system in all_three_state_systems()]


def sweep_summary(rows: list[dict[str, object]], label: str) -> dict[str, object]:
    reachable_not_closed = [row["id"] for row in rows if not row["reachable_closed"]]
    always_implies_eventually_failures = [
        row["id"]
        for row in rows
        if row["global_finality"] and not row["eventually_resolution"]
    ]
    return {
        "status": f"DLC-{label}-pass"
        if not reachable_not_closed and not always_implies_eventually_failures
        else f"DLC-{label}-fail",
        "system_count": len(rows),
        "reachable_not_closed": reachable_not_closed,
        "always_implies_eventually_failures": always_implies_eventually_failures,
        "eventual_resolution_not_global_finality_count": sum(
            1 for row in rows if row["eventual_resolution_not_global_finality"]
        ),
        "eventual_stability_not_eventual_resolution_count": sum(
            1 for row in rows if row["eventual_stability_not_eventual_resolution"]
        ),
        "stable_resolution_not_global_finality_count": sum(
            1 for row in rows if row["stable_resolution_not_global_finality"]
        ),
    }


def two_state_sweep_summary() -> dict[str, object]:
    return sweep_summary(two_state_sweep_records(), "two-state")


def three_state_sweep_summary() -> dict[str, object]:
    return sweep_summary(three_state_sweep_records(), "three-state")


def lean_named_witnesses() -> list[dict[str, object]]:
    return [
        {
            "lean_artifact": "eventual_resolution_not_global_finality",
            "system": TWO_DELTA.id,
            "eventually_resolution": True,
            "global_finality": False,
            "status": "DLC-lean-named-witness",
        },
        {
            "lean_artifact": "stable_resolution_not_global_finality",
            "system": TWO_DELTA.id,
            "eventually_stable_resolution": True,
            "global_finality": False,
            "status": "DLC-lean-named-witness",
        },
        {
            "lean_artifact": "eventual_stability_not_eventual_resolution",
            "system": LOOP_DELTA.id,
            "eventually_stable": True,
            "eventually_resolution": False,
            "status": "DLC-lean-named-witness",
        },
        {
            "lean_artifact": "twoDelta_all_states_closed",
            "record": "twoDeltaAllStates",
            "closed": True,
            "status": "DLC-lean-named-closure-witness",
        },
        {
            "lean_artifact": "twoDelta_start_only_not_closed",
            "record": "twoDeltaStartOnly",
            "closed": False,
            "status": "DLC-lean-named-closure-witness",
        },
        {
            "lean_artifact": "delta_reachable_closed",
            "record": "twoDeltaReachable",
            "closed": True,
            "status": "DLC-lean-named-closure-witness",
        },
    ]


def named_witnesses_are_supported() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    by_id = {row["id"]: row for row in coverage()}
    by_record = {row["id"]: row for row in closure_records()}
    missing = []
    for witness in lean_named_witnesses():
        if "system" in witness:
            row = by_id.get(witness["system"])
        else:
            row = by_record.get(witness["record"])
        if row is None:
            missing.append(witness)
            continue
        supported = True
        for key, value in witness.items():
            if key in {"lean_artifact", "system", "record", "status"}:
                continue
            supported = supported and row.get(key) == value
        if not supported:
            missing.append(witness)
    return lean_named_witnesses(), missing


def summary() -> dict[str, object]:
    rows = coverage()
    closure = closure_records()
    two_sweep = two_state_sweep_summary()
    three_sweep = three_state_sweep_summary()
    _named, missing_named = named_witnesses_are_supported()
    failed = (
        missing_named
        or two_sweep["status"] != "DLC-two-state-pass"
        or three_sweep["status"] != "DLC-three-state-pass"
    )
    return {
        "status": "DLC-pass" if not failed else "DLC-fail",
        "system_count": len(rows),
        "closure_record_count": len(closure),
        "two_state_sweep_system_count": two_sweep["system_count"],
        "three_state_sweep_system_count": three_sweep["system_count"],
        "lean_named_witness_count": len(lean_named_witnesses()),
        "missing_lean_named_witnesses": missing_named,
        "two_state_sweep_status": two_sweep["status"],
        "three_state_sweep_status": three_sweep["status"],
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    output_dir = root / "docs" / "delta_checks"
    output_dir.mkdir(parents=True, exist_ok=True)

    rows = coverage()
    closure = closure_records()
    sweep_records = two_state_sweep_records()
    sweep_summary = two_state_sweep_summary()
    three_sweep_records = three_state_sweep_records()
    three_sweep_summary = three_state_sweep_summary()
    named_witnesses, missing_named = named_witnesses_are_supported()
    payload = summary()

    (output_dir / "coverage.json").write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "lean_named_witnesses.json").write_text(
        json.dumps(named_witnesses, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "closure_records.json").write_text(
        json.dumps(closure, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "two_state_sweep.json").write_text(
        json.dumps(sweep_records, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "two_state_sweep_summary.json").write_text(
        json.dumps(sweep_summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "three_state_sweep.json").write_text(
        json.dumps(three_sweep_records, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "three_state_sweep_summary.json").write_text(
        json.dumps(three_sweep_summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(json.dumps(payload, indent=2, sort_keys=True))
    return 1 if payload["status"] != "DLC-pass" else 0


if __name__ == "__main__":
    raise SystemExit(main())
