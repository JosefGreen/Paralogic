from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Union


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Truth:
    pass


@dataclass(frozen=True)
class Falsity:
    pass


@dataclass(frozen=True)
class Conj:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Disj:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Impl:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Neg:
    body: "Formula"


Formula = Union[Var, Truth, Falsity, Conj, Disj, Impl, Neg]
Valuation = dict[str, bool]


def atoms(formula: Formula) -> set[str]:
    if isinstance(formula, Var):
        return {formula.name}
    if isinstance(formula, (Truth, Falsity)):
        return set()
    if isinstance(formula, (Conj, Disj, Impl)):
        return atoms(formula.left) | atoms(formula.right)
    if isinstance(formula, Neg):
        return atoms(formula.body)
    raise TypeError(formula)


def eval_formula(formula: Formula, valuation: Valuation) -> bool:
    if isinstance(formula, Var):
        return valuation[formula.name]
    if isinstance(formula, Truth):
        return True
    if isinstance(formula, Falsity):
        return False
    if isinstance(formula, Conj):
        return eval_formula(formula.left, valuation) and eval_formula(
            formula.right, valuation
        )
    if isinstance(formula, Disj):
        return eval_formula(formula.left, valuation) or eval_formula(
            formula.right, valuation
        )
    if isinstance(formula, Impl):
        return (not eval_formula(formula.left, valuation)) or eval_formula(
            formula.right, valuation
        )
    if isinstance(formula, Neg):
        return not eval_formula(formula.body, valuation)
    raise TypeError(formula)


def entails(premises: list[Formula], conclusion: Formula) -> bool:
    names = sorted(set().union(*(atoms(formula) for formula in premises), atoms(conclusion)))
    for values in itertools.product([False, True], repeat=len(names)):
        valuation = dict(zip(names, values))
        if all(eval_formula(formula, valuation) for formula in premises):
            if not eval_formula(conclusion, valuation):
                return False
    return True


def payload(formula: Formula) -> object:
    if isinstance(formula, Var):
        return {"var": formula.name}
    if isinstance(formula, Truth):
        return "truth"
    if isinstance(formula, Falsity):
        return "falsity"
    if isinstance(formula, Conj):
        return {"conj": [payload(formula.left), payload(formula.right)]}
    if isinstance(formula, Disj):
        return {"disj": [payload(formula.left), payload(formula.right)]}
    if isinstance(formula, Impl):
        return {"impl": [payload(formula.left), payload(formula.right)]}
    if isinstance(formula, Neg):
        return {"neg": payload(formula.body)}
    raise TypeError(formula)


P = Var("P")
Q = Var("Q")
R = Var("R")


TARGETS = [
    {
        "id": "PPC-CONJ-LEFT",
        "lean_artifact": "derives_conj_left_example_sound",
        "premises": [Conj(P, Q)],
        "conclusion": P,
        "expected": True,
    },
    {
        "id": "PPC-MODUS-PONENS",
        "lean_artifact": "derives_modus_ponens_example_sound",
        "premises": [Impl(P, Q), P],
        "conclusion": Q,
        "expected": True,
    },
    {
        "id": "PPC-IMPL-INTRO",
        "lean_artifact": "derives_implication_intro_example_sound",
        "premises": [Q],
        "conclusion": Impl(P, Q),
        "expected": True,
    },
    {
        "id": "PPC-FALSITY-ELIM",
        "lean_artifact": "derives_falsity_elim_example_sound",
        "premises": [Falsity()],
        "conclusion": P,
        "expected": True,
    },
    {
        "id": "PPC-DISJ-ELIM",
        "lean_artifact": "derives_disj_elim_example_sound",
        "premises": [Disj(P, Q), Impl(P, R), Impl(Q, R)],
        "conclusion": R,
        "expected": True,
    },
    {
        "id": "PPC-REJECT-AFFIRMING-CONSEQUENT",
        "lean_artifact": "no Lean derivation claimed",
        "premises": [Impl(P, Q), Q],
        "conclusion": P,
        "expected": False,
    },
    {
        "id": "PPC-REJECT-DISJUNCTIVE-AFFIRMATION",
        "lean_artifact": "no Lean derivation claimed",
        "premises": [Disj(P, Q), P],
        "conclusion": Q,
        "expected": False,
    },
]


def target_result(target: dict[str, object]) -> dict[str, object]:
    premises = target["premises"]
    conclusion = target["conclusion"]
    assert isinstance(premises, list)
    actual = entails(premises, conclusion)  # type: ignore[arg-type]
    expected = bool(target["expected"])
    return {
        "id": target["id"],
        "lean_artifact": target["lean_artifact"],
        "premises": [payload(formula) for formula in premises],
        "conclusion": payload(conclusion),  # type: ignore[arg-type]
        "expected": expected,
        "actual": actual,
        "passed": actual == expected,
    }


def coverage() -> dict[str, object]:
    results = [target_result(target) for target in TARGETS]
    return {
        "status": "PPC-pass" if all(row["passed"] for row in results)
        else "PPC-fail",
        "target_count": len(TARGETS),
        "results": results,
    }


def write_outputs(root: Path) -> None:
    out_dir = root / "docs" / "propositional_proof_checks"
    out_dir.mkdir(parents=True, exist_ok=True)
    cov = coverage()
    for row in cov["results"]:
        assert isinstance(row, dict)
        (out_dir / f"{row['id']}.json").write_text(
            json.dumps(row, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    (out_dir / "coverage.json").write_text(
        json.dumps(cov, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    write_outputs(root)
    cov = coverage()
    print(
        json.dumps(
            {
                "status": cov["status"],
                "target_count": cov["target_count"],
                "failed": [
                    row["id"]
                    for row in cov["results"]
                    if not row["passed"]
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if cov["status"] == "PPC-pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
