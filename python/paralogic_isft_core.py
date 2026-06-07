"""Finite Paralogic / ISFT core checker.

This module encodes a deliberately small, executable fragment of the
Paralogic / ISFT core:

- ISF is a definitional conjunction.
- M8 is a stricter definitional conjunction that includes all ISF premises.
- ValidInsight is a definitional conjunction requiring evaluator acceptance
  plus transition, transformation, defeater, generativity, and directionality
  guards.

The checker is exhaustive over the primitive atoms that affect each claim.
It may support EFC/EFE/PYC labels for this finite fragment only. It is not
Lean verification and it is not empirical validation.
"""

from __future__ import annotations

from dataclasses import dataclass
import itertools
from typing import Dict, Iterable, List, Sequence, Set


BoolModel = Dict[str, bool]


DEFINITIONS: Dict[str, Set[str]] = {
    "ISF": {"Uses", "Claims", "SupportDegraded", "TreatsAsAdequate"},
    "M8": {
        "Uses",
        "Claims",
        "PowerRelevant",
        "PowerValidityDependence",
        "PowerOmitted",
        "SupportDegraded",
        "TreatsAsAdequate",
    },
    "ValidInsight": {
        "CandidateInsight",
        "EvaluatorAccepts",
        "LicensedTransition",
        "NonTrivialTransformation",
        "ContradictionAddressed",
        "NoHigherOrderDefeater",
        "GenerativityMinimal",
        "DirectionalNonEquivalence",
    },
}


@dataclass(frozen=True)
class Check:
    id: str
    expected: str
    antecedent: Sequence[str]
    consequent: str
    note: str


CHECKS: List[Check] = [
    Check("EFE-ISF-01", "entails", ("ISF",), "Uses", "ISF unfolds to Uses."),
    Check("EFE-ISF-02", "entails", ("ISF",), "Claims", "ISF unfolds to Claims."),
    Check(
        "EFE-ISF-03",
        "entails",
        ("ISF",),
        "SupportDegraded",
        "ISF unfolds to SupportDegraded.",
    ),
    Check(
        "EFE-ISF-04",
        "entails",
        ("ISF",),
        "TreatsAsAdequate",
        "ISF unfolds to TreatsAsAdequate.",
    ),
    Check("EFE-M8-01", "entails", ("M8",), "ISF", "M8 contains all ISF conjuncts."),
    Check("EFC-ISF-01", "non_entails", ("Uses",), "ISF", "Use alone is insufficient."),
    Check(
        "EFC-ISF-02",
        "non_entails",
        ("Claims",),
        "ISF",
        "Claim-making alone is insufficient.",
    ),
    Check(
        "EFC-ISF-03",
        "non_entails",
        ("SupportDegraded",),
        "ISF",
        "Degraded support alone is insufficient.",
    ),
    Check(
        "EFC-ISF-04",
        "non_entails",
        ("Uses", "Claims", "SupportDegraded"),
        "ISF",
        "Adequacy treatment remains required.",
    ),
    Check("EFC-M8-01", "non_entails", ("ISF",), "M8", "ISF need not be power erasure."),
    Check(
        "EFC-M8-02",
        "non_entails",
        ("PowerRelevant",),
        "M8",
        "Power relevance alone is insufficient.",
    ),
    Check(
        "EFC-M8-03",
        "non_entails",
        ("PowerOmitted",),
        "M8",
        "Power omission alone is insufficient.",
    ),
    Check(
        "EFC-M8-04",
        "non_entails",
        ("M8",),
        "Discrimination",
        "M8 has no built-in discrimination bridge.",
    ),
    Check(
        "EFC-M8-05",
        "non_entails",
        ("M8",),
        "Coercion",
        "M8 has no built-in coercion bridge.",
    ),
    Check(
        "EFC-M8-06",
        "non_entails",
        ("M8",),
        "Harm",
        "M8 has no built-in harm bridge.",
    ),
    Check(
        "EFC-M8-07",
        "non_entails",
        ("M8",),
        "Illegality",
        "M8 has no built-in legal bridge.",
    ),
    Check(
        "EFC-M8-08",
        "non_entails",
        ("M8",),
        "MoralGuilt",
        "M8 has no built-in moral-guilt bridge.",
    ),
    Check(
        "EFC-M8-09",
        "non_entails",
        ("M8",),
        "RepairObligation",
        "M8 has no built-in repair-obligation bridge.",
    ),
    Check(
        "EFC-VI-01",
        "non_entails",
        ("CandidateInsight",),
        "ValidInsight",
        "Candidate insight is insufficient.",
    ),
    Check(
        "EFC-VI-02",
        "non_entails",
        ("FrameShift",),
        "ValidInsight",
        "Frame shift is insufficient.",
    ),
    Check(
        "EFC-VI-03",
        "non_entails",
        ("ValidInsight",),
        "EmpiricalTruth",
        "ValidInsight has no empirical-truth bridge.",
    ),
    Check(
        "EFC-VI-04",
        "non_entails",
        ("ValidInsight",),
        "MoralTruth",
        "ValidInsight has no moral-truth bridge.",
    ),
    Check(
        "EFC-VI-05",
        "non_entails",
        ("ValidInsight",),
        "Repair",
        "ValidInsight has no repair bridge.",
    ),
    Check(
        "EFE-EVAL-01",
        "entails",
        ("ValidInsight",),
        "EvaluatorAccepts",
        "Evaluator acceptance is necessary in this core definition.",
    ),
    Check(
        "EFC-EVAL-02",
        "non_entails",
        ("EvaluatorAccepts",),
        "ValidInsight",
        "Evaluator acceptance is not sufficient.",
    ),
    Check(
        "EFC-DELTA-01",
        "non_entails",
        ("DeltaResolution",),
        "EmpiricalTruth",
        "Delta resolution is not final truth.",
    ),
    Check(
        "EFC-AUDIT-01",
        "non_entails",
        ("EmpiricalValidation",),
        "GovernanceLegitimacy",
        "Empirical validation is not governance legitimacy.",
    ),
    Check(
        "EFC-AUDIT-02",
        "non_entails",
        ("Accountability",),
        "Repair",
        "Accountability is not repair by definition.",
    ),
]


PYC_TARGETS = [
    ("PYC-ISF-01", ("ISF",), "Uses"),
    ("PYC-ISF-02", ("ISF",), "Claims"),
    ("PYC-ISF-03", ("ISF",), "SupportDegraded"),
    ("PYC-ISF-04", ("ISF",), "TreatsAsAdequate"),
    ("PYC-M8-01", ("M8",), "ISF"),
    ("PYC-VI-01", ("ValidInsight",), "EvaluatorAccepts"),
]


def holds(atom: str, model: BoolModel) -> bool:
    if atom in DEFINITIONS:
        return all(holds(part, model) for part in DEFINITIONS[atom])
    return bool(model.get(atom, False))


def primitive_atoms_for(atom: str) -> Set[str]:
    if atom not in DEFINITIONS:
        return {atom}
    atoms: Set[str] = set()
    for part in DEFINITIONS[atom]:
        atoms.update(primitive_atoms_for(part))
    return atoms


def atoms_for_check(check: Check) -> List[str]:
    atoms: Set[str] = set()
    for atom in check.antecedent:
        atoms.update(primitive_atoms_for(atom))
    atoms.update(primitive_atoms_for(check.consequent))
    return sorted(atoms)


def all_models(atoms: Sequence[str]) -> Iterable[BoolModel]:
    for values in itertools.product((False, True), repeat=len(atoms)):
        yield dict(zip(atoms, values))


def find_countermodel(check: Check) -> BoolModel | None:
    atoms = atoms_for_check(check)
    for model in all_models(atoms):
        if all(holds(atom, model) for atom in check.antecedent) and not holds(
            check.consequent, model
        ):
            return model
    return None


def compact_witness(model: BoolModel, check: Check) -> Dict[str, bool]:
    keys: Set[str] = set(DEFINITIONS)
    keys.update(check.antecedent)
    keys.add(check.consequent)
    for atom in check.antecedent:
        keys.update(primitive_atoms_for(atom))
    keys.update(primitive_atoms_for(check.consequent))
    return {key: holds(key, model) for key in sorted(keys)}


def run_finite_check(check: Check) -> Dict[str, object]:
    witness = find_countermodel(check)
    actual = "entails" if witness is None else "non_entails"
    return {
        "id": check.id,
        "expected": check.expected,
        "actual": actual,
        "ok": actual == check.expected,
        "label": "EFE" if actual == "entails" else "EFC",
        "antecedent": list(check.antecedent),
        "consequent": check.consequent,
        "note": check.note,
        "countermodel": None if witness is None else compact_witness(witness, check),
    }


def proof_check_horn(antecedent: Sequence[str], consequent: str) -> Dict[str, object]:
    available: Set[str] = set()
    agenda: List[str] = list(antecedent)
    trace: List[str] = []

    while agenda:
        atom = agenda.pop(0)
        if atom in available:
            continue
        available.add(atom)
        trace.append(f"assume {atom}")
        if atom in DEFINITIONS:
            for part in sorted(DEFINITIONS[atom]):
                if part not in available:
                    agenda.append(part)
                    trace.append(f"unfold {atom} -> {part}")

    if consequent in available:
        return {"ok": True, "trace": trace}
    if consequent in DEFINITIONS and DEFINITIONS[consequent].issubset(available):
        trace.append(
            "fold "
            + consequent
            + " from "
            + ", ".join(sorted(DEFINITIONS[consequent]))
        )
        return {"ok": True, "trace": trace}
    return {"ok": False, "trace": trace}


def run_all_checks() -> Dict[str, object]:
    finite_checks = [run_finite_check(check) for check in CHECKS]
    pyc_checks = []
    for check_id, antecedent, consequent in PYC_TARGETS:
        result = proof_check_horn(antecedent, consequent)
        pyc_checks.append(
            {
                "id": check_id,
                "antecedent": list(antecedent),
                "consequent": consequent,
                "ok": result["ok"],
                "label": "PYC" if result["ok"] else "PYC-FAIL",
                "trace": result["trace"],
            }
        )

    return {
        "scope": "finite one-object Boolean fragment of selected Paralogic / ISFT definitions",
        "machine_check_claim": "EFC/EFE/PYC only; not Lean; not empirical validation",
        "definitions": {key: sorted(value) for key, value in DEFINITIONS.items()},
        "finite_checks": finite_checks,
        "pyc_checks": pyc_checks,
        "ok": all(item["ok"] for item in finite_checks)
        and all(item["ok"] for item in pyc_checks),
    }
