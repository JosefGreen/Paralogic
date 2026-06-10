from __future__ import annotations

import itertools
import json
from pathlib import Path


Score = str
Decision = str
Triple = tuple[Score, Score, Score]

SCORES: tuple[Score, ...] = ("low", "medium", "high")
DECISIONS: tuple[Decision, ...] = ("rejects", "abstains", "accepts")


def score_decision(score: Score) -> Decision:
    return {
        "low": "rejects",
        "medium": "abstains",
        "high": "accepts",
    }[score]


def score_accepts(score: Score) -> bool:
    return score_decision(score) == "accepts"


def score_rejects(score: Score) -> bool:
    return score_decision(score) == "rejects"


def score_abstains(score: Score) -> bool:
    return score_decision(score) == "abstains"


def decision_disagreement(left: Decision, right: Decision) -> bool:
    return left != right


def score_disagreement(left: Score, right: Score) -> bool:
    return decision_disagreement(score_decision(left), score_decision(right))


def at_least_two_accept(triple: Triple) -> bool:
    return sum(1 for score in triple if score_accepts(score)) >= 2


def at_least_two_reject(triple: Triple) -> bool:
    return sum(1 for score in triple if score_rejects(score)) >= 2


def majority_decision(triple: Triple) -> Decision:
    if at_least_two_accept(triple):
        return "accepts"
    if at_least_two_reject(triple):
        return "rejects"
    return "abstains"


def triple_payload(triple: Triple) -> dict[str, object]:
    return {
        "scores": list(triple),
        "score_decisions": [score_decision(score) for score in triple],
        "at_least_two_accept": at_least_two_accept(triple),
        "at_least_two_reject": at_least_two_reject(triple),
        "majority_decision": majority_decision(triple),
    }


def exhaustive_triples() -> list[Triple]:
    return list(itertools.product(SCORES, repeat=3))


def exhaustive_summary() -> dict[str, object]:
    rows = [triple_payload(triple) for triple in exhaustive_triples()]
    failures = []
    for row in rows:
        accepts = row["at_least_two_accept"]
        rejects = row["at_least_two_reject"]
        decision = row["majority_decision"]
        if accepts and decision != "accepts":
            failures.append(row)
        if rejects and decision != "rejects":
            failures.append(row)
        if not accepts and not rejects and decision != "abstains":
            failures.append(row)
    return {
        "status": "ECC-pass" if not failures else "ECC-fail",
        "score_count": len(SCORES),
        "triple_count": len(rows),
        "accept_majority_count": sum(
            1 for row in rows if row["majority_decision"] == "accepts"
        ),
        "reject_majority_count": sum(
            1 for row in rows if row["majority_decision"] == "rejects"
        ),
        "abstain_majority_count": sum(
            1 for row in rows if row["majority_decision"] == "abstains"
        ),
        "failures": failures,
    }


def lean_named_witnesses() -> list[dict[str, object]]:
    return [
        {
            "lean_artifact": "high_score_accepts",
            "supported": score_accepts("high"),
        },
        {
            "lean_artifact": "medium_score_abstains",
            "supported": score_abstains("medium"),
        },
        {
            "lean_artifact": "low_score_rejects",
            "supported": score_rejects("low"),
        },
        {
            "lean_artifact": "low_score_not_accepts",
            "supported": not score_accepts("low"),
        },
        {
            "lean_artifact": "medium_score_not_accepts",
            "supported": not score_accepts("medium"),
        },
        {
            "lean_artifact": "high_low_scores_disagree",
            "supported": score_disagreement("high", "low"),
        },
        {
            "lean_artifact": "high_medium_scores_disagree",
            "supported": score_disagreement("high", "medium"),
        },
        {
            "lean_artifact": "two_high_one_low_majority_accepts",
            "supported": majority_decision(("high", "high", "low"))
            == "accepts",
        },
        {
            "lean_artifact": "one_high_two_low_majority_rejects",
            "supported": majority_decision(("high", "low", "low"))
            == "rejects",
        },
        {
            "lean_artifact": "one_high_two_medium_majority_abstains",
            "supported": majority_decision(("high", "medium", "medium"))
            == "abstains",
        },
        {
            "lean_artifact": "atLeastTwoAccept_two_high_one_low",
            "supported": at_least_two_accept(("high", "high", "low")),
        },
        {
            "lean_artifact": "not_atLeastTwoAccept_one_high_two_medium",
            "supported": not at_least_two_accept(
                ("high", "medium", "medium")
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
    summary = exhaustive_summary()
    return {
        "status": "ECC-pass" if not missing and summary["status"] == "ECC-pass"
        else "ECC-fail",
        "lean_named_witnesses": witnesses,
        "missing_witnesses": missing,
        "summary": summary,
    }


def write_outputs(root: Path) -> None:
    out_dir = root / "docs" / "evaluator_calibration_checks"
    out_dir.mkdir(parents=True, exist_ok=True)
    payloads = {
        "triples.json": [triple_payload(triple) for triple in exhaustive_triples()],
        "summary.json": exhaustive_summary(),
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
                "triple_count": payload["summary"]["triple_count"],
                "missing_witnesses": payload["missing_witnesses"],
                "failures": payload["summary"]["failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["status"] == "ECC-pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
