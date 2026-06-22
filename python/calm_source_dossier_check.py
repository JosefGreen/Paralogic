from __future__ import annotations

import csv
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOSSIER = ROOT / "docs" / "calm" / "source_dossier"

REQUIRED_FILES = [
    "README.md",
    "source_register.csv",
    "case_claim_map.csv",
    "calm_applicability.csv",
    "maturity_rules.csv",
    "capture_gaps.csv",
    "internal_artifacts.csv",
    "chapter_source_matrix.csv",
    "SOURCE_CAPTURE_LOG.md",
    "manuscript_readiness_audit.md",
]


def read_csv(name: str) -> list[dict[str, str]]:
    with (DOSSIER / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def check() -> dict:
    missing_files = [name for name in REQUIRED_FILES if not (DOSSIER / name).exists()]
    source_rows = read_csv("source_register.csv") if not missing_files else []
    case_rows = read_csv("case_claim_map.csv") if not missing_files else []
    gap_rows = read_csv("capture_gaps.csv") if not missing_files else []
    chapter_rows = read_csv("chapter_source_matrix.csv") if not missing_files else []

    missing_case_packets = []
    for row in case_rows:
        slug = "".join(
            ch.lower() if ch.isalnum() else "-"
            for ch in row.get("Case / Source Cluster", "").strip()
        )
        while "--" in slug:
            slug = slug.replace("--", "-")
        slug = slug.strip("-") or "untitled"
        if not (DOSSIER / "case_packets" / f"{slug}.md").exists():
            missing_case_packets.append(row.get("Case / Source Cluster", ""))

    source_required_columns = {
        "ID",
        "Source Family",
        "Specific Source / Document",
        "Current Maturity",
        "Claims Supported",
        "Does NOT Prove",
        "Priority",
        "Source Class",
        "Readiness",
    }
    missing_source_columns = []
    if source_rows:
        missing_source_columns = sorted(source_required_columns - set(source_rows[0]))

    forbidden_ready = [
        row["ID"] for row in source_rows
        if row.get("Readiness") == "manuscript_ready_candidate"
        and "S5" not in row.get("Current Maturity", "")
        and "S6" not in row.get("Current Maturity", "")
    ]

    audit_text = (
        (DOSSIER / "manuscript_readiness_audit.md").read_text(encoding="utf-8")
        if (DOSSIER / "manuscript_readiness_audit.md").exists()
        else ""
    )
    audit_has_nonready_verdict = "Not yet manuscript-ready." in audit_text
    source_packet_count = len(list((DOSSIER / "source_packets").glob("*.md")))

    status = "CSD-pass"
    if (
        missing_files
        or len(source_rows) < 50
        or len(case_rows) < 15
        or len(gap_rows) < 1
        or len(chapter_rows) < len(case_rows)
        or missing_case_packets
        or missing_source_columns
        or forbidden_ready
        or not audit_has_nonready_verdict
        or source_packet_count < 7
    ):
        status = "CSD-fail"

    return {
        "status": status,
        "source_rows": len(source_rows),
        "case_rows": len(case_rows),
        "gap_rows": len(gap_rows),
        "chapter_rows": len(chapter_rows),
        "missing_files": missing_files,
        "missing_case_packets": missing_case_packets,
        "missing_source_columns": missing_source_columns,
        "forbidden_ready_promotions": forbidden_ready,
        "audit_has_nonready_verdict": audit_has_nonready_verdict,
        "source_packet_count": source_packet_count,
    }


if __name__ == "__main__":
    result = check()
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["status"] == "CSD-pass" else 1)
