from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PILOT_FILE = ROOT / "docs" / "REAL_WORLD_USEFULNESS_PILOTS.md"


def pilot_text() -> str:
    return PILOT_FILE.read_text(encoding="utf-8")


def usefulness_scores() -> list[int]:
    return [
        int(match.group(1))
        for match in re.finditer(r"^Usefulness score:\s+([0-5])\.", pilot_text(), re.MULTILINE)
    ]


def coverage() -> dict[str, object]:
    scores = usefulness_scores()
    average = sum(scores) / len(scores) if scores else 0.0
    threshold_pass = len(scores) >= 3 and min(scores) >= 3 and average >= 3.5
    return {
        "status": "UPC-pass" if threshold_pass else "UPC-fail",
        "pilot_count": len(scores),
        "usefulness_scores": scores,
        "average_usefulness": average,
        "minimum_usefulness": min(scores) if scores else None,
        "threshold": {
            "minimum_pilots": 3,
            "minimum_score": 3,
            "minimum_average": 3.5,
        },
    }


def main() -> None:
    payload = coverage()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if payload["status"] != "UPC-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
