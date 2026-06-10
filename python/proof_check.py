from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path


Atom = str


@dataclass(frozen=True)
class Rule:
    name: str
    premises: tuple[Atom, ...]
    conclusion: Atom


RULES: dict[str, Rule] = {
    "ISF_to_Uses": Rule("ISF_to_Uses", ("ISF",), "Uses"),
    "ISF_to_Claims": Rule("ISF_to_Claims", ("ISF",), "Claims"),
    "ISF_to_SupportDegraded": Rule(
        "ISF_to_SupportDegraded", ("ISF",), "SupportDegraded"
    ),
    "ISF_to_TreatsAsAdequate": Rule(
        "ISF_to_TreatsAsAdequate", ("ISF",), "TreatsAsAdequate"
    ),
    "M8_to_ISF": Rule("M8_to_ISF", ("M8",), "ISF"),
    "M8_to_Uses": Rule("M8_to_Uses", ("M8",), "Uses"),
    "M8_to_Claims": Rule("M8_to_Claims", ("M8",), "Claims"),
    "ValidInsight_to_EvaluatorAccepts": Rule(
        "ValidInsight_to_EvaluatorAccepts", ("ValidInsight",), "EvaluatorAccepts"
    ),
}


Trace = dict[str, object]


TRACES: list[Trace] = [
    {
        "id": "PYC-ISF-USES",
        "premises": ["ISF"],
        "steps": [
            {"kind": "premise", "atom": "ISF"},
            {
                "kind": "rule",
                "rule": "ISF_to_Uses",
                "refs": [0],
                "atom": "Uses",
            },
        ],
        "expected": "accept",
    },
    {
        "id": "PYC-M8-ISF",
        "premises": ["M8"],
        "steps": [
            {"kind": "premise", "atom": "M8"},
            {"kind": "rule", "rule": "M8_to_ISF", "refs": [0], "atom": "ISF"},
        ],
        "expected": "accept",
    },
    {
        "id": "PYC-M8-USES",
        "premises": ["M8"],
        "steps": [
            {"kind": "premise", "atom": "M8"},
            {"kind": "rule", "rule": "M8_to_Uses", "refs": [0], "atom": "Uses"},
        ],
        "expected": "accept",
    },
    {
        "id": "PYC-VALID-INSIGHT-EVAL",
        "premises": ["ValidInsight"],
        "steps": [
            {"kind": "premise", "atom": "ValidInsight"},
            {
                "kind": "rule",
                "rule": "ValidInsight_to_EvaluatorAccepts",
                "refs": [0],
                "atom": "EvaluatorAccepts",
            },
        ],
        "expected": "accept",
    },
    {
        "id": "PYC-REJECT-EVAL-TO-VALID-INSIGHT",
        "premises": ["EvaluatorAccepts"],
        "steps": [
            {"kind": "premise", "atom": "EvaluatorAccepts"},
            {
                "kind": "rule",
                "rule": "ValidInsight_to_EvaluatorAccepts",
                "refs": [0],
                "atom": "ValidInsight",
            },
        ],
        "expected": "reject",
    },
    {
        "id": "PYC-REJECT-MISSING-M8-PREMISE",
        "premises": ["ISF"],
        "steps": [
            {"kind": "premise", "atom": "ISF"},
            {"kind": "rule", "rule": "M8_to_Uses", "refs": [0], "atom": "Uses"},
        ],
        "expected": "reject",
    },
]


def check_trace(trace: Trace) -> dict[str, object]:
    premises = set(trace["premises"])
    derived: list[Atom] = []
    diagnostics: list[str] = []

    for index, step in enumerate(trace["steps"]):
        kind = step.get("kind")
        atom = step.get("atom")
        if not isinstance(atom, str):
            diagnostics.append(f"step {index}: atom must be a string")
            return result(trace, "reject", derived, diagnostics)

        if kind == "premise":
            if atom not in premises:
                diagnostics.append(f"step {index}: undeclared premise {atom}")
                return result(trace, "reject", derived, diagnostics)
            derived.append(atom)
            continue

        if kind == "rule":
            rule_name = step.get("rule")
            if not isinstance(rule_name, str) or rule_name not in RULES:
                diagnostics.append(f"step {index}: unknown rule {rule_name}")
                return result(trace, "reject", derived, diagnostics)
            rule = RULES[rule_name]
            refs = step.get("refs")
            if not isinstance(refs, list):
                diagnostics.append(f"step {index}: refs must be a list")
                return result(trace, "reject", derived, diagnostics)
            if atom != rule.conclusion:
                diagnostics.append(
                    f"step {index}: rule {rule.name} concludes {rule.conclusion}, not {atom}"
                )
                return result(trace, "reject", derived, diagnostics)
            referenced_atoms: list[Atom] = []
            for ref in refs:
                if not isinstance(ref, int) or ref < 0 or ref >= len(derived):
                    diagnostics.append(f"step {index}: invalid ref {ref}")
                    return result(trace, "reject", derived, diagnostics)
                referenced_atoms.append(derived[ref])
            missing = [premise for premise in rule.premises if premise not in referenced_atoms]
            if missing:
                diagnostics.append(
                    f"step {index}: rule {rule.name} missing premises {missing}"
                )
                return result(trace, "reject", derived, diagnostics)
            derived.append(atom)
            continue

        diagnostics.append(f"step {index}: unknown step kind {kind}")
        return result(trace, "reject", derived, diagnostics)

    return result(trace, "accept", derived, diagnostics)


def result(
    trace: Trace, status: str, derived: list[Atom], diagnostics: list[str]
) -> dict[str, object]:
    expected = trace["expected"]
    return {
        "id": trace["id"],
        "status": f"PYC-{status}",
        "expected": f"PYC-{expected}",
        "passed": status == expected,
        "derived": derived,
        "diagnostics": diagnostics,
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    output_dir = root / "docs" / "proof_checks"
    output_dir.mkdir(parents=True, exist_ok=True)

    results = [check_trace(trace) for trace in TRACES]
    for trace, trace_result in zip(TRACES, results):
        payload = {"trace": trace, "result": trace_result}
        (output_dir / f"{trace['id']}.json").write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    coverage = {
        "status": "PYC-pass" if all(item["passed"] for item in results) else "PYC-fail",
        "rule_count": len(RULES),
        "trace_count": len(TRACES),
        "results": results,
    }
    (output_dir / "coverage.json").write_text(
        json.dumps(coverage, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(coverage, indent=2))
    return 0 if coverage["status"] == "PYC-pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
