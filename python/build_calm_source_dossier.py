from __future__ import annotations

import argparse
import csv
import re
from collections import Counter, defaultdict
from pathlib import Path

import pandas as pd


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = Path(
    r"C:\Users\virgin\Downloads\paper_armies_calm_source_map_v1.xlsx"
)
OUT_DIR = ROOT / "docs" / "calm" / "source_dossier"


SHEET_CONFIG = {
    "Master Source Map": "ID",
    "Case-Claim Map": "Case / Source Cluster",
    "CALM Applicability": "CALM Component",
    "Maturity Rules": "Level",
    "Capture Gaps": "Gap ID",
    "Internal Artifacts": "Artifact",
}


def slug(value: str) -> str:
    text = re.sub(r"[^A-Za-z0-9]+", "-", value.strip()).strip("-").lower()
    return text or "untitled"


def clean(value) -> str:
    if pd.isna(value):
        return ""
    return str(value).strip()


def read_table(path: Path, sheet: str, first_header: str) -> list[dict[str, str]]:
    raw = pd.read_excel(path, sheet_name=sheet, header=None).fillna("")
    header_idx = None
    for idx, row in raw.iterrows():
        if clean(row.iloc[0]) == first_header:
            header_idx = idx
            break
    if header_idx is None:
        raise ValueError(f"Could not find header {first_header!r} in sheet {sheet!r}")

    headers = [clean(cell) for cell in raw.iloc[header_idx].tolist()]
    rows: list[dict[str, str]] = []
    for _, row in raw.iloc[header_idx + 1 :].iterrows():
        values = [clean(cell) for cell in row.tolist()]
        if not any(values):
            continue
        record = {
            headers[i] or f"Column {i + 1}": values[i]
            for i in range(min(len(headers), len(values)))
        }
        if any(record.values()):
            rows.append(record)
    return rows


def write_csv(path: Path, rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def priority_counts(rows: list[dict[str, str]]) -> Counter:
    return Counter(row.get("Priority", "Unspecified") or "Unspecified" for row in rows)


def maturity_ready(row: dict[str, str]) -> bool:
    maturity = row.get("Current Maturity", "")
    return "S5" in maturity or "S6" in maturity


def source_kind(row: dict[str, str]) -> str:
    family = row.get("Source Family", "").lower()
    source_type = row.get("Source Type", "").lower()
    authority = row.get("Authority Tier", "").lower()
    if "internal" in source_type or "internal" in authority or "paralogic" in family:
        return "internal_methodology"
    if "journal" in source_type or "discovery" in authority:
        return "discovery_or_narrative"
    if "official" in source_type or "official" in authority or "primary" in authority:
        return "external_evidence_target"
    if "think tank" in source_type or "rand" in family or "aerospace" in family:
        return "policy_or_theory_support"
    return "supporting_source_target"


def readiness(row: dict[str, str]) -> str:
    next_action = row.get("Next Action", "").lower()
    if maturity_ready(row) and "extract" not in next_action and "capture" not in next_action:
        return "manuscript_ready_candidate"
    if "capture" in next_action or "extract" in next_action:
        return "capture_or_page_extraction_required"
    if source_kind(row) == "internal_methodology":
        return "methodology_only_not_case_evidence"
    return "triage_required"


def chapter_rows(case_rows: list[dict[str, str]]) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for row in case_rows:
        chapters = re.split(r"[,;/]\s*", row.get("Primary Chapter(s)", ""))
        for chapter in [c.strip() for c in chapters if c.strip()]:
            out.append(
                {
                    "Chapter": chapter,
                    "Case / Source Cluster": row.get("Case / Source Cluster", ""),
                    "Role": row.get("Role", ""),
                    "Main Claim Supported": row.get("Main Claim Supported", ""),
                    "CALM Lens": row.get("CALM Lens", ""),
                    "Risk / Overclaim Guard": row.get("Risk / Overclaim Guard", ""),
                    "Source Need": row.get("Source Need", ""),
                }
            )
    return sorted(out, key=lambda r: (r["Chapter"], r["Case / Source Cluster"]))


def md_table(rows: list[dict[str, str]], columns: list[str]) -> str:
    lines = [
        "| " + " | ".join(columns) + " |",
        "| " + " | ".join("---" for _ in columns) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join((row.get(col, "") or "").replace("|", "/") for col in columns)
            + " |"
        )
    return "\n".join(lines)


def write_case_packets(case_rows: list[dict[str, str]]) -> None:
    case_dir = OUT_DIR / "case_packets"
    case_dir.mkdir(parents=True, exist_ok=True)
    for row in case_rows:
        name = row.get("Case / Source Cluster", "Untitled Case")
        path = case_dir / f"{slug(name)}.md"
        text = f"""# Case Packet: {name}

## Role

{row.get("Role", "")}

## Chapter Placement

{row.get("Primary Chapter(s)", "")}

## Main Claim Supported

{row.get("Main Claim Supported", "")}

## CALM Lens

{row.get("CALM Lens", "")}

## Overclaim Guard

{row.get("Risk / Overclaim Guard", "")}

## Source Need

{row.get("Source Need", "")}

## Manuscript Readiness

Not manuscript-ready until the source need above is satisfied with page-level
evidence, counter-evidence, and a source maturity rating of S5 or stronger for
primary factual claims.

## Usefulness Check

This packet preserves the intended narrative/doctrinal role while preventing a
case from proving more than the evidence supports.

## Claim Boundary

This packet does not establish the factual claim. It records what the case is
allowed to support after source capture and what inference must remain blocked.
"""
        path.write_text(text, encoding="utf-8")


def write_index(
    source_rows: list[dict[str, str]],
    case_rows: list[dict[str, str]],
    gap_rows: list[dict[str, str]],
) -> None:
    counts = priority_counts(source_rows)
    kinds = Counter(source_kind(row) for row in source_rows)
    readiness_counts = Counter(readiness(row) for row in source_rows)
    critical = [row for row in source_rows if row.get("Priority") == "Critical"]
    text = f"""# CALM / Paper Armies Source Dossier

## Status

This dossier is generated from `paper_armies_calm_source_map_v1.xlsx`. It turns
the spreadsheet into an auditable source-dossier package, but it does not claim
that every source has been captured or that every chapter claim is
manuscript-ready.

The current governing rule is strict: no primary factual manuscript claim is
ready until it has direct source capture, page-level extraction, counter-evidence
review, and source maturity S5 or stronger.

## Inventory

- Master source rows: {len(source_rows)}
- Case/source-cluster rows: {len(case_rows)}
- Capture gaps: {len(gap_rows)}
- Critical source rows: {counts.get("Critical", 0)}
- High source rows: {counts.get("High", 0)}
- Medium source rows: {counts.get("Medium", 0)}

## Source Classes

{md_table([{"Class": k, "Count": str(v)} for k, v in sorted(kinds.items())], ["Class", "Count"])}

## Readiness Classes

{md_table([{"Readiness": k, "Count": str(v)} for k, v in sorted(readiness_counts.items())], ["Readiness", "Count"])}

## Critical Source Queue

{md_table(critical, ["ID", "Source Family", "Specific Source / Document", "Paper Armies Use", "CALM Mapping", "Next Action"])}

## Dossier Files

- `source_register.csv` - normalized master source map.
- `case_claim_map.csv` - normalized case-to-claim map.
- `calm_applicability.csv` - CALM component/source-pattern mapping.
- `capture_gaps.csv` - open source and evidence gaps.
- `chapter_source_matrix.csv` - chapter-to-case support matrix.
- `case_packets/` - one packet per case/source cluster.
- `source_packets/` - captured source packets as public anchors and page-level
  extraction work are completed.
- `SOURCE_CAPTURE_LOG.md` - source-capture progress and readiness levels.
- `manuscript_readiness_audit.md` - anti-reward-hacking readiness audit.

## Usefulness Check

This dossier gives Paper Armies and CALM a source-control layer. It separates
external evidence from internal methodology, prevents discovery sources from
becoming factual proof, and gives each case a bounded role before drafting.

## Claim Boundary

This dossier does not prove the book thesis, does not validate CALM, does not
complete source capture, and does not authorize factual claims unsupported by
page-level public evidence.
"""
    (OUT_DIR / "README.md").write_text(text, encoding="utf-8")


def write_readiness_audit(
    source_rows: list[dict[str, str]],
    case_rows: list[dict[str, str]],
    gap_rows: list[dict[str, str]],
) -> None:
    blockers = []
    for row in source_rows:
        if row.get("Priority") in {"Critical", "High"} and readiness(row) != "manuscript_ready_candidate":
            blockers.append(
                {
                    "ID": row.get("ID", ""),
                    "Source Family": row.get("Source Family", ""),
                    "Priority": row.get("Priority", ""),
                    "Current Maturity": row.get("Current Maturity", ""),
                    "Blocker": readiness(row),
                    "Next Action": row.get("Next Action", ""),
                }
            )
    text = f"""# Manuscript Readiness Audit

## Executive Verdict

Not yet manuscript-ready.

The attached spreadsheet is strong as a source map, but it honestly labels many
entries as target maturity rather than captured evidence. Treating it as a
finished source dossier would be reward hacking.

## What Is Complete In This Pass

- The workbook has been normalized into a source-register package.
- Every source row is classified by source role and readiness.
- Every case/source cluster has a case packet.
- Chapter-to-case support has been extracted into a matrix.
- Open capture gaps are preserved rather than hidden.

## Blocking Conditions

{md_table(blockers[:40], ["ID", "Source Family", "Priority", "Current Maturity", "Blocker", "Next Action"])}

## Source-Capture Gates

1. Capture the highest-maturity public source, preferably official.
2. Extract page-level evidence for each claim.
3. Record counter-evidence or limitations.
4. State what the source does not prove.
5. Link the source to a chapter claim and CALM concept.
6. Run legal/security/human-cost guardrails for sensitive cases.
7. Only then mark a claim as manuscript-ready.

## Human-Grounding Gate

Human-cost cases require official or high-maturity public records, no invented
private thoughts, no classified inference, and no use of casualties as
rhetorical props.

## Solution-Support Gate

CALM instruments may be supported by cases only when the source shows the
failure mode or corrective pattern directly. Internal Paralogic/CALM materials
can support method design, not factual defense claims.

## Usefulness Check

This audit prevents the dossier from looking complete just because it is
organized. It identifies the exact source-capture work required before drafting
claims at manuscript level.

## Claim Boundary

This audit does not complete the source dossier. It states why the current
dossier is not yet manuscript-ready and defines the gates required to make it
so.
"""
    (OUT_DIR / "manuscript_readiness_audit.md").write_text(text, encoding="utf-8")


def build(input_path: Path) -> dict:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    tables = {
        sheet: read_table(input_path, sheet, first_header)
        for sheet, first_header in SHEET_CONFIG.items()
    }

    source_rows = tables["Master Source Map"]
    for row in source_rows:
        row["Source Class"] = source_kind(row)
        row["Readiness"] = readiness(row)

    write_csv(OUT_DIR / "source_register.csv", source_rows)
    write_csv(OUT_DIR / "case_claim_map.csv", tables["Case-Claim Map"])
    write_csv(OUT_DIR / "calm_applicability.csv", tables["CALM Applicability"])
    write_csv(OUT_DIR / "maturity_rules.csv", tables["Maturity Rules"])
    write_csv(OUT_DIR / "capture_gaps.csv", tables["Capture Gaps"])
    write_csv(OUT_DIR / "internal_artifacts.csv", tables["Internal Artifacts"])
    write_csv(OUT_DIR / "chapter_source_matrix.csv", chapter_rows(tables["Case-Claim Map"]))
    write_case_packets(tables["Case-Claim Map"])
    write_index(source_rows, tables["Case-Claim Map"], tables["Capture Gaps"])
    write_readiness_audit(source_rows, tables["Case-Claim Map"], tables["Capture Gaps"])

    return {
        "status": "built",
        "source_rows": len(source_rows),
        "case_rows": len(tables["Case-Claim Map"]),
        "gap_rows": len(tables["Capture Gaps"]),
        "output": str(OUT_DIR),
        "readiness_counts": dict(Counter(readiness(row) for row in source_rows)),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    args = parser.parse_args()
    result = build(args.input)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
