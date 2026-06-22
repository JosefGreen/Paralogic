from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

REQUIRED_DOCS = [
    "docs/calm/PROJECT_CHARTER.md",
    "docs/calm/COMPLETION_PIPELINE.md",
    "docs/calm/PAPER_ARMIES_ARCHITECTURE.md",
    "docs/calm/SOURCE_CASE_DOSSIER_TEMPLATE.md",
    "docs/calm/CALM_FORMAL_SPEC.md",
]

REQUIRED_PHRASES = {
    "docs/calm/PROJECT_CHARTER.md": [
        "CALM means Capability Assurance and Learning Mobility.",
        "Professional experience supplies the lens.",
        "Make false confidence harder to move. Make valid learning easier to reuse.",
    ],
    "docs/calm/COMPLETION_PIPELINE.md": [
        "No phase may be marked complete unless",
        "No CALM metric may be used without a Metric Integrity Test",
        "No learning claim may be promoted from captured to learned without second valid use",
    ],
    "docs/calm/PAPER_ARMIES_ARCHITECTURE.md": [
        "Paper Armies: A Doctrine for Defense Reform",
        "The Map Outranks the Terrain",
        "The Force That Can Keep Its Books",
    ],
    "docs/calm/SOURCE_CASE_DOSSIER_TEMPLATE.md": [
        "Source Maturity Scale",
        "Claim not supported",
        "Human-cost cases require extra care.",
    ],
    "docs/calm/CALM_FORMAL_SPEC.md": [
        "ClaimReceipt",
        "LearningPacket",
        "CALMImplementation",
    ],
}

REQUIRED_LEAN_DECLARATIONS = [
    "ClaimReceipt",
    "ClaimTravelReady",
    "PaperCapabilityRisk",
    "missing_boundary_blocks_claim_travel",
    "claim_travel_ready_does_not_prove_operational_validity",
    "LearningPacket",
    "LearningTravelReady",
    "learning_travel_ready_does_not_prove_second_valid_use",
    "CALMImplementation",
    "PaperCALMRisk",
    "artifacts_alone_do_not_pass_reflexivity",
]


def check() -> dict:
    missing_docs = [
        path for path in REQUIRED_DOCS if not (ROOT / path).exists()
    ]
    phrase_failures: dict[str, list[str]] = {}
    for path, phrases in REQUIRED_PHRASES.items():
        full_path = ROOT / path
        text = full_path.read_text(encoding="utf-8") if full_path.exists() else ""
        missing = [phrase for phrase in phrases if phrase not in text]
        if missing:
            phrase_failures[path] = missing

    lean_path = ROOT / "src" / "Paralogic" / "CALM.lean"
    lean_text = lean_path.read_text(encoding="utf-8") if lean_path.exists() else ""
    missing_lean = [
        declaration for declaration in REQUIRED_LEAN_DECLARATIONS
        if declaration not in lean_text
    ]

    claim_boundary_missing = []
    usefulness_missing = []
    for path in REQUIRED_DOCS:
        full_path = ROOT / path
        text = full_path.read_text(encoding="utf-8") if full_path.exists() else ""
        if "## Claim Boundary" not in text:
            claim_boundary_missing.append(path)
        if "## Usefulness Check" not in text:
            usefulness_missing.append(path)

    status = "CALM-pass"
    if (
        missing_docs
        or phrase_failures
        or missing_lean
        or claim_boundary_missing
        or usefulness_missing
    ):
        status = "CALM-fail"

    return {
        "status": status,
        "required_doc_count": len(REQUIRED_DOCS),
        "missing_docs": missing_docs,
        "phrase_failures": phrase_failures,
        "missing_lean_declarations": missing_lean,
        "claim_boundary_missing": claim_boundary_missing,
        "usefulness_check_missing": usefulness_missing,
    }


if __name__ == "__main__":
    result = check()
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["status"] == "CALM-pass" else 1)
