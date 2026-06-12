from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXACT_CLAIM = (
    '"This is a Lean-checked formal research workbench for selected '
    'Paralogic/ISFT fragments, not a complete system."'
)
REQUIRED_FILES = (
    ROOT / "README.md",
    ROOT / "docs" / "MATHEMATICAL_SERIOUSNESS_CLAIM.md",
)
SCAN_FILES = (
    ROOT / "README.md",
    ROOT / "docs" / "CURRENT_STATUS.md",
    ROOT / "docs" / "MATHEMATICAL_SERIOUSNESS_CLAIM.md",
    ROOT / "docs" / "CLAIM_DISCIPLINE_AUDIT.md",
)
RISK_PATTERNS = (
    "complete system",
    "empirically validated",
    "peer reviewed",
    "proven useful",
    "institution-ready",
    "commercial",
    "compliance",
    "proves wrongdoing",
    "proves harm",
    "proves illegality",
    "proves moral guilt",
    "proves discrimination",
    "proves governance illegitimacy",
)
NEGATING_MARKERS = (
    "not ",
    "not a ",
    "do not ",
    "does not ",
    "forbidden",
    "unsafe",
    "without",
    "absent",
    "incomplete",
)


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def exact_claim_results() -> dict[str, bool]:
    return {str(path.relative_to(ROOT)): EXACT_CLAIM in text(path) for path in REQUIRED_FILES}


def risky_line_is_negated(line: str) -> bool:
    lowered = line.lower()
    return any(marker in lowered for marker in NEGATING_MARKERS)


def warning_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for path in SCAN_FILES:
        if not path.exists():
            continue
        current_heading = ""
        suppressed_block = False
        lines = text(path).splitlines()
        for line_no, line in enumerate(lines, start=1):
            if line.startswith("#"):
                current_heading = line.lower()
                suppressed_block = False
            if "do not claim:" in line.lower():
                suppressed_block = True
            if line.lower().startswith("permitted current claim"):
                suppressed_block = False
            if "does not yet contain:" in line.lower():
                suppressed_block = True
            if line.lower().startswith("canonical audit:"):
                suppressed_block = False
            lowered = line.lower()
            if suppressed_block:
                continue
            if any(
                marker in current_heading
                for marker in (
                    "do not",
                    "forbidden",
                    "unsafe",
                    "what this repository is not",
                    "scan method",
                    "overclaim findings",
                )
            ):
                continue
            previous_line = lines[line_no - 2] if line_no >= 2 else ""
            next_line = lines[line_no] if line_no < len(lines) else ""
            context = f"{previous_line} {line} {next_line}"
            for pattern in RISK_PATTERNS:
                if pattern in lowered and not risky_line_is_negated(context):
                    rows.append(
                        {
                            "file": str(path.relative_to(ROOT)),
                            "line": line_no,
                            "pattern": pattern,
                            "text": line.strip(),
                        }
                    )
    return rows


def coverage() -> dict[str, object]:
    exact = exact_claim_results()
    warnings = warning_rows()
    return {
        "status": "CDC-pass" if all(exact.values()) else "CDC-fail",
        "exact_claim": EXACT_CLAIM,
        "exact_claim_results": exact,
        "warning_count": len(warnings),
        "warnings": warnings,
    }


def main() -> None:
    payload = coverage()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if payload["status"] != "CDC-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
