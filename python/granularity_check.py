from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from pathlib import Path


Item = str
Relation = frozenset[tuple[Item, Item]]

ITEMS: tuple[Item, ...] = ("favorable", "corroborating", "unfavorable")
SUPPORTS: dict[Item, bool] = {
    "favorable": True,
    "corroborating": True,
    "unfavorable": False,
}


@dataclass(frozen=True)
class GranularityResult:
    relation: Relation
    item: Item
    lower: bool
    upper: bool
    boundary: bool


def all_reflexive_relations(items: tuple[Item, ...] = ITEMS) -> list[Relation]:
    required = {(item, item) for item in items}
    optional = [
        (left, right)
        for left in items
        for right in items
        if left != right
    ]
    relations = []
    for mask in itertools.product([False, True], repeat=len(optional)):
        pairs = set(required)
        for include, pair in zip(mask, optional):
            if include:
                pairs.add(pair)
        relations.append(frozenset(pairs))
    return relations


def lower(relation: Relation, item: Item) -> bool:
    return SUPPORTS[item] and all(
        SUPPORTS[other]
        for other in ITEMS
        if (item, other) in relation
    )


def upper(relation: Relation, item: Item) -> bool:
    return any(
        (item, other) in relation and SUPPORTS[other]
        for other in ITEMS
    )


def result_for(relation: Relation, item: Item) -> GranularityResult:
    is_lower = lower(relation, item)
    is_upper = upper(relation, item)
    return GranularityResult(
        relation=relation,
        item=item,
        lower=is_lower,
        upper=is_upper,
        boundary=is_upper and not is_lower,
    )


def refines(fine: Relation, coarse: Relation) -> bool:
    return fine.issubset(coarse)


def relation_payload(relation: Relation) -> list[list[Item]]:
    return [[left, right] for left, right in sorted(relation)]


def relation_from_payload(payload: list[list[Item]]) -> Relation:
    return frozenset((left, right) for left, right in payload)


def check_refinement_law() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    rows = []
    failures = []
    relations = all_reflexive_relations()
    for coarse in relations:
        for fine in relations:
            if not refines(fine, coarse):
                continue
            for item in ITEMS:
                coarse_lower = lower(coarse, item)
                fine_lower = lower(fine, item)
                passed = (not coarse_lower) or fine_lower
                row = {
                    "item": item,
                    "coarse_relation": relation_payload(coarse),
                    "fine_relation": relation_payload(fine),
                    "coarse_lower": coarse_lower,
                    "fine_lower": fine_lower,
                    "status": "GRC-pass" if passed else "GRC-fail",
                }
                rows.append(row)
                if not passed:
                    failures.append(row)
    return rows, failures


def converse_failures() -> list[dict[str, object]]:
    witnesses = []
    relations = all_reflexive_relations()
    for coarse in relations:
        for fine in relations:
            if not refines(fine, coarse):
                continue
            for item in ITEMS:
                if lower(fine, item) and not lower(coarse, item):
                    witnesses.append(
                        {
                            "item": item,
                            "coarse_relation": relation_payload(coarse),
                            "fine_relation": relation_payload(fine),
                            "fine_lower": True,
                            "coarse_lower": False,
                            "status": "GRC-converse-failure-witness",
                        }
                    )
    return witnesses


def identity_relation() -> Relation:
    return frozenset((item, item) for item in ITEMS)


def all_true_relation() -> Relation:
    return frozenset((left, right) for left in ITEMS for right in ITEMS)


def lean_named_witnesses() -> list[dict[str, object]]:
    return [
        {
            "lean_artifact": "mask_payload_converse_failure",
            "item": "favorable",
            "coarse_relation": relation_payload(all_true_relation()),
            "fine_relation": relation_payload(identity_relation()),
            "fine_lower": lower(identity_relation(), "favorable"),
            "coarse_lower": lower(all_true_relation(), "favorable"),
            "status": "GRC-lean-named-witness",
        }
    ]


def named_witnesses_are_generated() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    generated = converse_failures()
    missing = []
    for named in lean_named_witnesses():
        candidate = {
            "item": named["item"],
            "coarse_relation": named["coarse_relation"],
            "fine_relation": named["fine_relation"],
            "fine_lower": named["fine_lower"],
            "coarse_lower": named["coarse_lower"],
            "status": "GRC-converse-failure-witness",
        }
        if candidate not in generated:
            missing.append(named)
    return lean_named_witnesses(), missing


def summary() -> dict[str, object]:
    rows, failures = check_refinement_law()
    witnesses = converse_failures()
    _named, missing_named = named_witnesses_are_generated()
    return {
        "status": "GRC-pass" if not failures else "GRC-fail",
        "item_count": len(ITEMS),
        "relation_count": len(all_reflexive_relations()),
        "refinement_case_count": len(rows),
        "converse_failure_count": len(witnesses),
        "lean_named_witness_count": len(lean_named_witnesses()),
        "missing_lean_named_witnesses": missing_named,
        "failed": failures,
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    output_dir = root / "docs" / "granularity_checks"
    output_dir.mkdir(parents=True, exist_ok=True)

    rows, failures = check_refinement_law()
    witnesses = converse_failures()
    named_witnesses, missing_named = named_witnesses_are_generated()
    payload = summary()

    (output_dir / "coverage.json").write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "converse_failures.json").write_text(
        json.dumps(witnesses, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "lean_named_witnesses.json").write_text(
        json.dumps(named_witnesses, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(json.dumps(payload, indent=2, sort_keys=True))
    return 1 if failures or missing_named else 0


if __name__ == "__main__":
    raise SystemExit(main())
