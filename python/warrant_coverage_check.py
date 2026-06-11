from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src" / "Paralogic" / "WarrantDischarge.lean"
OUT_DIR = ROOT / "docs" / "warrant_coverage_checks"


REQUIRED_THEOREMS: tuple[str, ...] = (
    "OperationalWarrantCoverageComplete",
    "all_warrant_obligations_operationally_discharged",
    "operational_warrant_coverage_complete",
    "operational_core_ne_source_backed",
    "operational_core_ne_empirically_validated",
)


def source_text() -> str:
    return SOURCE.read_text(encoding="utf-8")


def extract_inductive_block(text: str, name: str) -> str:
    pattern = re.compile(
        rf"inductive\s+{re.escape(name)}\s+where(?P<body>.*?)(?:\n\S)",
        re.DOTALL,
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"could not locate inductive {name}")
    return match.group("body")


def extract_def_block(text: str, name: str) -> str:
    pattern = re.compile(
        rf"def\s+{re.escape(name)}\s*:[\s\S]*?(?=\n(?:def|theorem|structure|inductive)\s|\Z)",
        re.MULTILINE,
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"could not locate def {name}")
    return match.group(0)


def warrant_obligations(text: str | None = None) -> list[str]:
    text = source_text() if text is None else text
    block = extract_inductive_block(text, "WarrantObligation")
    return re.findall(r"^\s*\|\s+([A-Za-z0-9_']+)", block, flags=re.MULTILINE)


def operational_core_cases(text: str | None = None) -> list[str]:
    text = source_text() if text is None else text
    block = extract_def_block(text, "warrantResolutionStatusWithOperationalCore")
    return re.findall(
        r"\|\s+WarrantObligation\.([A-Za-z0-9_']+)\s*=>\s*\n\s*WarrantResolutionStatus\.operationallyDischarged",
        block,
    )


def theorem_presence(text: str | None = None) -> dict[str, bool]:
    text = source_text() if text is None else text
    return {name: name in text for name in REQUIRED_THEOREMS}


def coverage() -> dict[str, object]:
    text = source_text()
    obligations = warrant_obligations(text)
    operational = operational_core_cases(text)
    missing = sorted(set(obligations) - set(operational))
    extra = sorted(set(operational) - set(obligations))
    theorem_status = theorem_presence(text)
    missing_theorems = [
        name for name, present in theorem_status.items() if not present
    ]
    return {
        "status": (
            "WCC-pass"
            if not missing and not extra and not missing_theorems
            else "WCC-fail"
        ),
        "obligation_count": len(obligations),
        "operational_case_count": len(operational),
        "obligations": obligations,
        "operational_cases": operational,
        "missing_operational_cases": missing,
        "extra_operational_cases": extra,
        "required_theorems": theorem_status,
        "missing_theorems": missing_theorems,
    }


def write_artifacts() -> dict[str, object]:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = coverage()
    (OUT_DIR / "coverage.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (OUT_DIR / "obligations.json").write_text(
        json.dumps(payload["obligations"], indent=2) + "\n",
        encoding="utf-8",
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if payload["status"] != "WCC-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
