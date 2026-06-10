from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


Atom = str
Valuation = dict[Atom, bool]
Formula = Callable[[Valuation], bool]


ATOMS: list[Atom] = [
    "uses",
    "claims",
    "supportDegraded",
    "treatsAsAdequate",
    "powerRelevant",
    "powerValidityDependence",
    "powerOmitted",
    "candidateInsight",
    "evaluatorAccepts",
    "licensedTransition",
    "nonTrivialTransformation",
    "contradictionAddressed",
    "noHigherOrderDefeater",
    "generativityMinimal",
    "directionalNonEquivalence",
    "deltaResolution",
    "empiricalTruth",
    "repair",
    "harm",
    "moralGuilt",
    "governanceLegitimacy",
    "empiricalValidation",
]


def atom(name: Atom) -> Formula:
    return lambda v: v.get(name, False)


def isf(v: Valuation) -> bool:
    return (
        v.get("uses", False)
        and v.get("claims", False)
        and v.get("supportDegraded", False)
        and v.get("treatsAsAdequate", False)
    )


def m8(v: Valuation) -> bool:
    return (
        isf(v)
        and v.get("powerRelevant", False)
        and v.get("powerValidityDependence", False)
        and v.get("powerOmitted", False)
    )


def valid_insight(v: Valuation) -> bool:
    return (
        v.get("candidateInsight", False)
        and v.get("evaluatorAccepts", False)
        and v.get("licensedTransition", False)
        and v.get("nonTrivialTransformation", False)
        and v.get("contradictionAddressed", False)
        and v.get("noHigherOrderDefeater", False)
        and v.get("generativityMinimal", False)
        and v.get("directionalNonEquivalence", False)
    )


@dataclass(frozen=True)
class Target:
    id: str
    description: str
    atoms: tuple[Atom, ...]
    premises: tuple[Formula, ...]
    conclusion: Formula
    expects_counterexample: bool


TARGETS: tuple[Target, ...] = (
    Target(
        id="EFC-ISF-USES-NOT-ISF",
        description="Uses does not entail ISF.",
        atoms=("uses", "claims", "supportDegraded", "treatsAsAdequate"),
        premises=(atom("uses"),),
        conclusion=isf,
        expects_counterexample=True,
    ),
    Target(
        id="EFC-ISF-IMPLIES-USES",
        description="ISF entails Uses.",
        atoms=("uses", "claims", "supportDegraded", "treatsAsAdequate"),
        premises=(isf,),
        conclusion=atom("uses"),
        expects_counterexample=False,
    ),
    Target(
        id="EFC-M8-ISF-NOT-M8",
        description="ISF does not entail M8.",
        atoms=(
            "uses",
            "claims",
            "supportDegraded",
            "treatsAsAdequate",
            "powerRelevant",
            "powerValidityDependence",
            "powerOmitted",
        ),
        premises=(isf,),
        conclusion=m8,
        expects_counterexample=True,
    ),
    Target(
        id="EFC-M8-IMPLIES-ISF",
        description="M8 entails ISF.",
        atoms=(
            "uses",
            "claims",
            "supportDegraded",
            "treatsAsAdequate",
            "powerRelevant",
            "powerValidityDependence",
            "powerOmitted",
        ),
        premises=(m8,),
        conclusion=isf,
        expects_counterexample=False,
    ),
    Target(
        id="EFC-M8-NOT-HARM",
        description="M8 does not entail harm.",
        atoms=(
            "uses",
            "claims",
            "supportDegraded",
            "treatsAsAdequate",
            "powerRelevant",
            "powerValidityDependence",
            "powerOmitted",
            "harm",
        ),
        premises=(m8,),
        conclusion=atom("harm"),
        expects_counterexample=True,
    ),
    Target(
        id="EFC-EVAL-NOT-VALID-INSIGHT",
        description="Evaluator acceptance does not entail ValidInsight.",
        atoms=(
            "candidateInsight",
            "evaluatorAccepts",
            "licensedTransition",
            "nonTrivialTransformation",
            "contradictionAddressed",
            "noHigherOrderDefeater",
            "generativityMinimal",
            "directionalNonEquivalence",
        ),
        premises=(atom("evaluatorAccepts"),),
        conclusion=valid_insight,
        expects_counterexample=True,
    ),
    Target(
        id="EFC-VALID-INSIGHT-IMPLIES-EVAL",
        description="ValidInsight entails evaluator acceptance.",
        atoms=(
            "candidateInsight",
            "evaluatorAccepts",
            "licensedTransition",
            "nonTrivialTransformation",
            "contradictionAddressed",
            "noHigherOrderDefeater",
            "generativityMinimal",
            "directionalNonEquivalence",
        ),
        premises=(valid_insight,),
        conclusion=atom("evaluatorAccepts"),
        expects_counterexample=False,
    ),
    Target(
        id="EFC-VALID-INSIGHT-NOT-EMPIRICAL-TRUTH",
        description="ValidInsight does not entail empirical truth.",
        atoms=(
            "candidateInsight",
            "evaluatorAccepts",
            "licensedTransition",
            "nonTrivialTransformation",
            "contradictionAddressed",
            "noHigherOrderDefeater",
            "generativityMinimal",
            "directionalNonEquivalence",
            "empiricalTruth",
        ),
        premises=(valid_insight,),
        conclusion=atom("empiricalTruth"),
        expects_counterexample=True,
    ),
    Target(
        id="EFC-VALID-INSIGHT-NOT-REPAIR",
        description="ValidInsight does not entail repair.",
        atoms=(
            "candidateInsight",
            "evaluatorAccepts",
            "licensedTransition",
            "nonTrivialTransformation",
            "contradictionAddressed",
            "noHigherOrderDefeater",
            "generativityMinimal",
            "directionalNonEquivalence",
            "repair",
        ),
        premises=(valid_insight,),
        conclusion=atom("repair"),
        expects_counterexample=True,
    ),
    Target(
        id="EFC-EMPIRICAL-VALIDATION-NOT-GOVERNANCE",
        description="Empirical validation does not entail governance legitimacy.",
        atoms=("empiricalValidation", "governanceLegitimacy"),
        premises=(atom("empiricalValidation"),),
        conclusion=atom("governanceLegitimacy"),
        expects_counterexample=True,
    ),
)


def valuations(atoms: tuple[Atom, ...]) -> list[Valuation]:
    rows: list[Valuation] = []
    for bits in itertools.product([False, True], repeat=len(atoms)):
        valuation = {name: value for name, value in zip(atoms, bits)}
        for atom_name in ATOMS:
            valuation.setdefault(atom_name, False)
        rows.append(valuation)
    return rows


def find_counterexample(target: Target) -> tuple[Valuation | None, int]:
    checked = 0
    for valuation in valuations(target.atoms):
        checked += 1
        if all(premise(valuation) for premise in target.premises):
            if not target.conclusion(valuation):
                return valuation, checked
    return None, checked


def project_witness(target: Target, valuation: Valuation | None) -> dict[str, bool] | None:
    if valuation is None:
        return None
    return {name: valuation[name] for name in target.atoms}


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    output_dir = root / "docs" / "finite_checks"
    output_dir.mkdir(parents=True, exist_ok=True)

    coverage = []
    witnesses = []
    failed = []

    for target in TARGETS:
        witness, checked = find_counterexample(target)
        found = witness is not None
        passed = found == target.expects_counterexample
        row = {
            "id": target.id,
            "description": target.description,
            "status": "EFC-bounded-pass" if passed else "EFC-bounded-fail",
            "valuation_scope": list(target.atoms),
            "valuation_count": 2 ** len(target.atoms),
            "valuations_checked_until_witness_or_exhaustion": checked,
            "expects_counterexample": target.expects_counterexample,
            "counterexample_found": found,
            "witness_file": f"{target.id}.json" if found else None,
        }
        coverage.append(row)
        if found:
            witness_payload = {
                "id": target.id,
                "description": target.description,
                "status": "EFC-bounded-witness",
                "valuation_scope": list(target.atoms),
                "valuation": project_witness(target, witness),
            }
            witnesses.append(witness_payload)
            (output_dir / f"{target.id}.json").write_text(
                json.dumps(witness_payload, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
        if not passed:
            failed.append(row)

    (output_dir / "coverage.json").write_text(
        json.dumps(coverage, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_dir / "witnesses.json").write_text(
        json.dumps(witnesses, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(json.dumps({"targets": len(TARGETS), "failed": failed}, indent=2))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
