from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ISFT_SOURCE = ROOT / "src" / "Paralogic" / "ISFTMechanisms.lean"
SYNTHESIS_SOURCE = ROOT / "src" / "Paralogic" / "MechanismSynthesis.lean"
OUT_DIR = ROOT / "docs" / "mechanism_coverage_checks"


MAPPING_DEFS: dict[str, Path] = {
    "mechanismIndex": ISFT_SOURCE,
    "mechanismName": ISFT_SOURCE,
    "mechanismLens": SYNTHESIS_SOURCE,
    "mechanismFailureAxis": SYNTHESIS_SOURCE,
}

REQUIRED_THEOREMS: tuple[str, ...] = (
    "allISFTMechanisms_length",
    "allISFTMechanisms_covers",
    "allISFTMechanisms_no_duplicates",
    "unit_candidate_mapping_certified",
    "unit_candidate_surface_certified",
    "all_candidate_mechanisms_not_source_backed",
    "all_candidate_mechanisms_not_empirically_validated",
    "CandidateMechanismCoverageComplete",
    "candidate_mechanism_coverage_complete",
)

UNIT_CANDIDATE_REQUIRED_TEXT: tuple[str, ...] = (
    "maturity := MechanismSemanticMaturity.candidateSynthesized",
    "lens := mechanismLens mechanism",
    "failureAxis := mechanismFailureAxis mechanism",
    "sourceTraceDeclared := True",
    "lensFitDeclared := True",
    "operationalTriggerDeclared := True",
    "failureContrastDeclared := True",
    "boundaryGuardDeclared := True",
    "empiricalCodingPlanDeclared := True",
    "nonCollapseGuardDeclared := True",
)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def all_source_text() -> str:
    return read(ISFT_SOURCE) + "\n" + read(SYNTHESIS_SOURCE)


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
        rf"def\s+{re.escape(name)}\s*[\s\S]*?"
        rf"(?=\n(?:def|theorem|structure|inductive)\s|\Z)",
        re.MULTILINE,
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"could not locate def {name}")
    return match.group(0)


def mechanisms(text: str | None = None) -> list[str]:
    text = read(ISFT_SOURCE) if text is None else text
    block = extract_inductive_block(text, "ISFTMechanism")
    return re.findall(r"^\s*\|\s+([A-Za-z0-9_']+)", block, flags=re.MULTILINE)


def mechanism_cases_in_def(def_name: str) -> list[str]:
    source = read(MAPPING_DEFS[def_name])
    block = extract_def_block(source, def_name)
    return re.findall(r"\|\s+ISFTMechanism\.([A-Za-z0-9_']+)", block)


def listed_mechanisms() -> list[str]:
    block = extract_def_block(read(SYNTHESIS_SOURCE), "allISFTMechanisms")
    return re.findall(r"ISFTMechanism\.([A-Za-z0-9_']+)", block)


def theorem_presence(text: str | None = None) -> dict[str, bool]:
    text = all_source_text() if text is None else text
    return {name: name in text for name in REQUIRED_THEOREMS}


def unit_candidate_surface_status() -> dict[str, bool]:
    block = extract_def_block(read(SYNTHESIS_SOURCE), "unitCandidateDefinition")
    return {needle: needle in block for needle in UNIT_CANDIDATE_REQUIRED_TEXT}


def mapping_coverage() -> dict[str, dict[str, object]]:
    declared = mechanisms()
    declared_set = set(declared)
    rows: dict[str, dict[str, object]] = {}
    for def_name in MAPPING_DEFS:
        cases = mechanism_cases_in_def(def_name)
        rows[def_name] = {
            "case_count": len(cases),
            "cases": cases,
            "missing_cases": sorted(declared_set - set(cases)),
            "extra_cases": sorted(set(cases) - declared_set),
            "duplicate_cases": sorted(
                mechanism for mechanism in set(cases) if cases.count(mechanism) > 1
            ),
        }
    return rows


def coverage() -> dict[str, object]:
    declared = mechanisms()
    listed = listed_mechanisms()
    theorem_status = theorem_presence()
    missing_theorems = [
        name for name, present in theorem_status.items() if not present
    ]
    unit_status = unit_candidate_surface_status()
    missing_unit_fields = [
        needle for needle, present in unit_status.items() if not present
    ]
    mappings = mapping_coverage()
    mapping_failures = {
        name: row
        for name, row in mappings.items()
        if row["missing_cases"] or row["extra_cases"] or row["duplicate_cases"]
    }
    duplicate_declared = sorted(
        mechanism for mechanism in set(declared) if declared.count(mechanism) > 1
    )
    duplicate_listed = sorted(
        mechanism for mechanism in set(listed) if listed.count(mechanism) > 1
    )
    listed_missing = sorted(set(declared) - set(listed))
    listed_extra = sorted(set(listed) - set(declared))

    status = (
        "MCC-pass"
        if len(declared) == 12
        and not duplicate_declared
        and len(listed) == 12
        and not duplicate_listed
        and not listed_missing
        and not listed_extra
        and not mapping_failures
        and not missing_theorems
        and not missing_unit_fields
        else "MCC-fail"
    )
    return {
        "status": status,
        "mechanism_count": len(declared),
        "mechanisms": declared,
        "duplicate_declared_mechanisms": duplicate_declared,
        "listed_mechanism_count": len(listed),
        "listed_mechanisms": listed,
        "duplicate_listed_mechanisms": duplicate_listed,
        "listed_missing_mechanisms": listed_missing,
        "listed_extra_mechanisms": listed_extra,
        "mapping_coverage": mappings,
        "mapping_failures": mapping_failures,
        "unit_candidate_required_fields": unit_status,
        "missing_unit_candidate_fields": missing_unit_fields,
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
    (OUT_DIR / "mechanisms.json").write_text(
        json.dumps(payload["mechanisms"], indent=2) + "\n",
        encoding="utf-8",
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if payload["status"] != "MCC-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
