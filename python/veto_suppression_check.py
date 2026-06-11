from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src" / "Paralogic" / "VetoSuppression.lean"
OUT_DIR = ROOT / "docs" / "veto_suppression_checks"


REQUIRED_CONDITIONS: tuple[str, ...] = (
    "vetoRightDeclared",
    "affectedParticipantPresent",
    "vetoAttemptMade",
    "vetoSuppressed",
    "suppressionMaterial",
    "reviewPathAbsent",
    "boundaryGuardAbsent",
)

REQUIRED_POSITIVE_ARTIFACTS: tuple[str, ...] = (
    "VetoSuppressionProfile",
    "VetoSuppressionProfileSatisfied",
    "VetoSuppressionProfile_to_supportDegraded",
    "VetoSuppressionProfile.toMechanismProfile",
    "VetoSuppressionProfile_to_mechanism_satisfied",
    "M9VetoSuppressionCase",
    "M9VetoSuppressionSatisfied",
    "M9VetoSuppressionCase_to_ISFSem",
    "vetoSuppressionOnlyProfile_satisfied",
    "vetoSuppressionOnly_supportDegraded",
    "vetoSuppressionOnly_to_ISFSem",
    "vetoSuppressionOnly_mechanism_profile_satisfied",
)

REQUIRED_BLOCKERS: tuple[str, ...] = (
    "missing_veto_right_blocks_profile",
    "missing_affected_participant_blocks_profile",
    "absent_veto_attempt_blocks_profile",
    "unsuppressed_veto_blocks_profile",
    "immaterial_veto_suppression_blocks_profile",
    "present_veto_review_blocks_profile",
    "present_veto_boundary_blocks_profile",
)

REQUIRED_BLOCKED_WITNESSES: tuple[str, ...] = (
    "vetoSuppressionNoRightProfile_blocked",
    "vetoSuppressionNoParticipantProfile_blocked",
    "vetoSuppressionNoAttemptProfile_blocked",
    "vetoSuppressionNotSuppressedProfile_blocked",
    "vetoSuppressionImmaterialProfile_blocked",
    "vetoSuppressionReviewPresentProfile_blocked",
    "vetoSuppressionBoundaryPresentProfile_blocked",
)


def source_text() -> str:
    return SOURCE.read_text(encoding="utf-8")


def extract_structure_block(text: str, name: str) -> str:
    pattern = re.compile(
        rf"structure\s+{re.escape(name)}[\s\S]*?"
        rf"(?=\n(?:def|theorem|structure|inductive)\s|\Z)",
        re.MULTILINE,
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"could not locate structure {name}")
    return match.group(0)


def required_presence(
    names: tuple[str, ...], text: str | None = None
) -> dict[str, bool]:
    text = source_text() if text is None else text
    return {name: name in text for name in names}


def condition_coverage(text: str | None = None) -> dict[str, dict[str, bool]]:
    text = source_text() if text is None else text
    profile_block = extract_structure_block(text, "VetoSuppressionProfile")
    satisfied_block = extract_structure_block(
        text, "VetoSuppressionProfileSatisfied"
    )
    blocked_block = re.search(
        r"def\s+VetoSuppressionProfileBlocked[\s\S]*?"
        r"(?=\ntheorem\s+missing_veto_right_blocks_profile)",
        text,
    )
    if blocked_block is None:
        raise ValueError("could not locate VetoSuppressionProfileBlocked")
    blocked_text = blocked_block.group(0)
    return {
        condition: {
            "in_profile": condition in profile_block,
            "in_satisfied": condition in satisfied_block,
            "in_blocked": condition in blocked_text,
        }
        for condition in REQUIRED_CONDITIONS
    }


def coverage() -> dict[str, object]:
    text = source_text()
    conditions = condition_coverage(text)
    missing_condition_mentions = {
        condition: places
        for condition, places in conditions.items()
        if not all(places.values())
    }
    positive = required_presence(REQUIRED_POSITIVE_ARTIFACTS, text)
    blockers = required_presence(REQUIRED_BLOCKERS, text)
    blocked_witnesses = required_presence(REQUIRED_BLOCKED_WITNESSES, text)
    missing_positive = [name for name, present in positive.items() if not present]
    missing_blockers = [name for name, present in blockers.items() if not present]
    missing_blocked_witnesses = [
        name for name, present in blocked_witnesses.items() if not present
    ]
    status = (
        "M9C-pass"
        if not missing_condition_mentions
        and not missing_positive
        and not missing_blockers
        and not missing_blocked_witnesses
        else "M9C-fail"
    )
    return {
        "status": status,
        "condition_count": len(REQUIRED_CONDITIONS),
        "conditions": conditions,
        "missing_condition_mentions": missing_condition_mentions,
        "positive_artifacts": positive,
        "missing_positive_artifacts": missing_positive,
        "blocker_count": len(REQUIRED_BLOCKERS),
        "blockers": blockers,
        "missing_blockers": missing_blockers,
        "blocked_witness_count": len(REQUIRED_BLOCKED_WITNESSES),
        "blocked_witnesses": blocked_witnesses,
        "missing_blocked_witnesses": missing_blocked_witnesses,
    }


def write_artifacts() -> dict[str, object]:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = coverage()
    (OUT_DIR / "coverage.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (OUT_DIR / "conditions.json").write_text(
        json.dumps(list(REQUIRED_CONDITIONS), indent=2) + "\n",
        encoding="utf-8",
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if payload["status"] != "M9C-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
