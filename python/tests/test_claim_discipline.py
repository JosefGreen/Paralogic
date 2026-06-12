from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def load_module(name: str, relative_path: str):
    path = ROOT / relative_path
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


claim_discipline_check = load_module(
    "claim_discipline_check", "python/claim_discipline_check.py"
)
usefulness_pilot_check = load_module(
    "usefulness_pilot_check", "python/usefulness_pilot_check.py"
)


def test_exact_safe_claim_is_present_in_public_files():
    coverage = claim_discipline_check.coverage()
    assert coverage["status"] == "CDC-pass"
    assert all(coverage["exact_claim_results"].values())


def test_usefulness_pilots_meet_threshold():
    coverage = usefulness_pilot_check.coverage()
    assert coverage["status"] == "UPC-pass"
    assert coverage["pilot_count"] >= 3
    assert coverage["minimum_usefulness"] >= 3
    assert coverage["average_usefulness"] >= 3.5
