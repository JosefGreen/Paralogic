from __future__ import annotations

import itertools
import json
from pathlib import Path


State = str
Action = str
ActionMap = dict[Action, State]

STATES: tuple[State, ...] = (
    "unrepaired",
    "underRepaired",
    "adequate",
    "overRepaired",
)

ACTIONS: tuple[Action, ...] = (
    "noAction",
    "partialAction",
    "targetedAction",
    "excessiveAction",
)

LEAN_ACTION_MAP: ActionMap = {
    "noAction": "unrepaired",
    "partialAction": "underRepaired",
    "targetedAction": "adequate",
    "excessiveAction": "overRepaired",
}

POSTULATE_STATES: tuple[State, ...] = (
    "failed",
    "adequate",
    "redundant",
    "overreach",
)

POSTULATE_ACTIONS: tuple[Action, ...] = (
    "failedAction",
    "adequateAction",
    "redundantAction",
    "overreachAction",
)

POSTULATE_ACTION_MAP: ActionMap = {
    "failedAction": "failed",
    "adequateAction": "adequate",
    "redundantAction": "redundant",
    "overreachAction": "overreach",
}

RANK: dict[State, int] = {
    "adequate": 0,
    "overRepaired": 1,
    "underRepaired": 2,
    "unrepaired": 3,
}


def acceptable(state: State) -> bool:
    return state in {"adequate", "overRepaired"}


def leq(candidate: State, incumbent: State) -> bool:
    return RANK[candidate] <= RANK[incumbent]


def strictly_preferred(candidate: State, incumbent: State) -> bool:
    return leq(candidate, incumbent) and not leq(incumbent, candidate)


def minimal_acceptable(state: State) -> bool:
    return acceptable(state) and not any(
        acceptable(candidate) and strictly_preferred(candidate, state)
        for candidate in STATES
    )


def minimal_states() -> list[State]:
    return [state for state in STATES if minimal_acceptable(state)]


def action_successful(mapping: ActionMap, action: Action) -> bool:
    return acceptable(mapping[action])


def action_minimal(mapping: ActionMap, action: Action) -> bool:
    return minimal_acceptable(mapping[action])


def action_conservative(mapping: ActionMap, action: Action) -> bool:
    return mapping[action] != "overRepaired"


def action_postulates(mapping: ActionMap, action: Action) -> bool:
    return (
        action_successful(mapping, action)
        and action_minimal(mapping, action)
        and action_conservative(mapping, action)
    )


def action_row(mapping: ActionMap, action: Action) -> dict[str, object]:
    result = mapping[action]
    return {
        "action": action,
        "result": result,
        "success": action_successful(mapping, action),
        "minimal": action_minimal(mapping, action),
        "conservative": action_conservative(mapping, action),
        "revision_postulates": action_postulates(mapping, action),
    }


def postulate_acceptable(state: State) -> bool:
    return state in {"adequate", "redundant", "overreach"}


def postulate_leq(candidate: State, incumbent: State) -> bool:
    return (candidate, incumbent) in {
        ("adequate", "adequate"),
        ("adequate", "redundant"),
        ("adequate", "failed"),
        ("redundant", "redundant"),
        ("redundant", "failed"),
        ("overreach", "overreach"),
        ("overreach", "failed"),
        ("failed", "failed"),
    }


def postulate_strictly_preferred(candidate: State, incumbent: State) -> bool:
    return (
        postulate_leq(candidate, incumbent)
        and not postulate_leq(incumbent, candidate)
    )


def postulate_minimal_acceptable(state: State) -> bool:
    return postulate_acceptable(state) and not any(
        postulate_acceptable(candidate)
        and postulate_strictly_preferred(candidate, state)
        for candidate in POSTULATE_STATES
    )


def postulate_action_successful(mapping: ActionMap, action: Action) -> bool:
    return postulate_acceptable(mapping[action])


def postulate_action_minimal(mapping: ActionMap, action: Action) -> bool:
    return postulate_minimal_acceptable(mapping[action])


def postulate_action_conservative(mapping: ActionMap, action: Action) -> bool:
    return mapping[action] != "overreach"


def postulate_action_package(mapping: ActionMap, action: Action) -> bool:
    return (
        postulate_action_successful(mapping, action)
        and postulate_action_minimal(mapping, action)
        and postulate_action_conservative(mapping, action)
    )


def postulate_action_row(mapping: ActionMap, action: Action) -> dict[str, object]:
    result = mapping[action]
    return {
        "action": action,
        "result": result,
        "success": postulate_action_successful(mapping, action),
        "minimal": postulate_action_minimal(mapping, action),
        "conservative": postulate_action_conservative(mapping, action),
        "postulate_package": postulate_action_package(mapping, action),
    }


def lean_action_table() -> list[dict[str, object]]:
    return [action_row(LEAN_ACTION_MAP, action) for action in ACTIONS]


def postulate_independence_table() -> list[dict[str, object]]:
    return [
        postulate_action_row(POSTULATE_ACTION_MAP, action)
        for action in POSTULATE_ACTIONS
    ]


def postulate_independence_summary() -> dict[str, object]:
    by_action = {row["action"]: row for row in postulate_independence_table()}
    expected = {
        "adequateAction": {
            "success": True,
            "minimal": True,
            "conservative": True,
            "postulate_package": True,
        },
        "redundantAction": {
            "success": True,
            "minimal": False,
            "conservative": True,
            "postulate_package": False,
        },
        "overreachAction": {
            "success": True,
            "minimal": True,
            "conservative": False,
            "postulate_package": False,
        },
        "failedAction": {
            "success": False,
            "minimal": False,
            "conservative": True,
            "postulate_package": False,
        },
    }
    failures = []
    for action, expected_row in expected.items():
        for key, value in expected_row.items():
            if by_action[action][key] != value:
                failures.append({
                    "action": action,
                    "field": key,
                    "expected": value,
                    "actual": by_action[action][key],
                })
    return {
        "status": "RRC-independence-pass" if not failures
        else "RRC-independence-fail",
        "states": list(POSTULATE_STATES),
        "actions": list(POSTULATE_ACTIONS),
        "minimal_states": [
            state
            for state in POSTULATE_STATES
            if postulate_minimal_acceptable(state)
        ],
        "failures": failures,
    }


def all_action_maps() -> list[ActionMap]:
    maps = []
    for results in itertools.product(STATES, repeat=len(ACTIONS)):
        maps.append(dict(zip(ACTIONS, results)))
    return maps


def exhaustive_action_sweep() -> dict[str, object]:
    failures: list[dict[str, object]] = []
    postulate_action_count = 0
    successful_but_not_postulate_count = 0
    overrepair_success_not_postulate_count = 0

    for index, mapping in enumerate(all_action_maps()):
        for action in ACTIONS:
            row = action_row(mapping, action)
            expected = mapping[action] == "adequate"
            actual = bool(row["revision_postulates"])
            if actual:
                postulate_action_count += 1
            if row["success"] and not actual:
                successful_but_not_postulate_count += 1
            if mapping[action] == "overRepaired" and row["success"] and not actual:
                overrepair_success_not_postulate_count += 1
            if actual != expected:
                failures.append({
                    "map_index": index,
                    "mapping": mapping,
                    "action": action,
                    "expected_revision_postulates": expected,
                    "actual_revision_postulates": actual,
                    "row": row,
                })

    return {
        "status": "RRC-pass" if not failures else "RRC-fail",
        "state_count": len(STATES),
        "action_count": len(ACTIONS),
        "action_map_count": len(all_action_maps()),
        "action_evaluation_count": len(all_action_maps()) * len(ACTIONS),
        "minimal_states": minimal_states(),
        "postulate_action_count": postulate_action_count,
        "successful_but_not_postulate_count": successful_but_not_postulate_count,
        "overrepair_success_not_postulate_count": (
            overrepair_success_not_postulate_count
        ),
        "postulate_equivalence_failures": failures,
    }


def lean_named_witnesses() -> list[dict[str, object]]:
    by_action = {row["action"]: row for row in lean_action_table()}
    sweep = exhaustive_action_sweep()
    return [
        {
            "lean_artifact": "rankedRepair_adequate_minimal",
            "supported": minimal_acceptable("adequate"),
        },
        {
            "lean_artifact": "rankedRepair_over_not_minimal",
            "supported": not minimal_acceptable("overRepaired"),
        },
        {
            "lean_artifact": "rankedRepair_has_unique_minimal",
            "supported": minimal_states() == ["adequate"],
        },
        {
            "lean_artifact": "rankedRepair_unique_minimal_from_best",
            "supported": (
                minimal_states() == ["adequate"]
                and all(leq("adequate", state) for state in STATES
                    if acceptable(state))
            ),
        },
        {
            "lean_artifact": "targetedRepair_satisfies_revision_postulates",
            "supported": by_action["targetedAction"]["revision_postulates"],
        },
        {
            "lean_artifact": "partialRepair_not_successful",
            "supported": not by_action["partialAction"]["success"],
        },
        {
            "lean_artifact": "doNothingRepair_not_successful",
            "supported": not by_action["noAction"]["success"],
        },
        {
            "lean_artifact": "excessiveRepair_successful_not_minimal",
            "supported": (
                by_action["excessiveAction"]["success"]
                and not by_action["excessiveAction"]["minimal"]
            ),
        },
        {
            "lean_artifact": "excessiveRepair_not_conservative",
            "supported": not by_action["excessiveAction"]["conservative"],
        },
        {
            "lean_artifact": "excessiveRepair_not_revision_postulates",
            "supported": not by_action["excessiveAction"]["revision_postulates"],
        },
        {
            "lean_artifact": "repairBridgeOnlyTargetedRevision_warrants_obligation",
            "supported": by_action["targetedAction"]["revision_postulates"],
        },
        {
            "lean_artifact": "adequateAction_satisfies_independence_package",
            "supported": postulate_action_package(
                POSTULATE_ACTION_MAP, "adequateAction"
            ),
        },
        {
            "lean_artifact": "redundantAction_success_conservative_not_minimal",
            "supported": (
                postulate_action_successful(
                    POSTULATE_ACTION_MAP, "redundantAction"
                )
                and postulate_action_conservative(
                    POSTULATE_ACTION_MAP, "redundantAction"
                )
                and not postulate_action_minimal(
                    POSTULATE_ACTION_MAP, "redundantAction"
                )
            ),
        },
        {
            "lean_artifact": "overreachAction_success_minimal_not_conservative",
            "supported": (
                postulate_action_successful(
                    POSTULATE_ACTION_MAP, "overreachAction"
                )
                and postulate_action_minimal(
                    POSTULATE_ACTION_MAP, "overreachAction"
                )
                and not postulate_action_conservative(
                    POSTULATE_ACTION_MAP, "overreachAction"
                )
            ),
        },
        {
            "lean_artifact": "failedAction_conservative_not_successful",
            "supported": (
                postulate_action_conservative(
                    POSTULATE_ACTION_MAP, "failedAction"
                )
                and not postulate_action_successful(
                    POSTULATE_ACTION_MAP, "failedAction"
                )
            ),
        },
        {
            "lean_artifact": "repair revision exhaustive action sweep",
            "supported": sweep["status"] == "RRC-pass",
        },
        {
            "lean_artifact": "repair postulate independence table",
            "supported": (
                postulate_independence_summary()["status"]
                == "RRC-independence-pass"
            ),
        },
    ]


def named_witnesses_are_supported() -> tuple[list[dict[str, object]], list[str]]:
    witnesses = lean_named_witnesses()
    missing = [
        str(row["lean_artifact"])
        for row in witnesses
        if not row["supported"]
    ]
    return witnesses, missing


def coverage() -> dict[str, object]:
    witnesses, missing = named_witnesses_are_supported()
    sweep = exhaustive_action_sweep()
    return {
        "status": "RRC-pass" if (
            not missing
            and sweep["status"] == "RRC-pass"
            and postulate_independence_summary()["status"]
            == "RRC-independence-pass"
        )
        else "RRC-fail",
        "lean_named_witnesses": witnesses,
        "missing_witnesses": missing,
        "sweep": sweep,
        "postulate_independence": postulate_independence_summary(),
    }


def write_outputs(root: Path) -> None:
    out_dir = root / "docs" / "repair_revision_checks"
    out_dir.mkdir(parents=True, exist_ok=True)
    payloads = {
        "action_table.json": lean_action_table(),
        "postulate_independence_table.json": postulate_independence_table(),
        "postulate_independence_summary.json": (
            postulate_independence_summary()
        ),
        "sweep_summary.json": exhaustive_action_sweep(),
        "lean_named_witnesses.json": lean_named_witnesses(),
        "coverage.json": coverage(),
    }
    for filename, payload in payloads.items():
        (out_dir / filename).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    write_outputs(root)
    payload = coverage()
    print(
        json.dumps(
            {
                "status": payload["status"],
                "action_map_count": payload["sweep"]["action_map_count"],
                "action_evaluation_count": (
                    payload["sweep"]["action_evaluation_count"]
                ),
                "postulate_equivalence_failures": len(
                    payload["sweep"]["postulate_equivalence_failures"]
                ),
                "postulate_independence_status": (
                    payload["postulate_independence"]["status"]
                ),
                "missing_witnesses": payload["missing_witnesses"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["status"] == "RRC-pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
