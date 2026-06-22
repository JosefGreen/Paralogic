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


calm_pipeline_check = load_module(
    "calm_pipeline_check", "python/calm_pipeline_check.py"
)


def test_calm_pipeline_package_is_complete_for_current_slice():
    result = calm_pipeline_check.check()
    assert result["status"] == "CALM-pass"
    assert result["missing_docs"] == []
    assert result["phrase_failures"] == {}
    assert result["missing_lean_declarations"] == []
    assert result["claim_boundary_missing"] == []
    assert result["usefulness_check_missing"] == []


def test_calm_pipeline_has_phase_zero_docs():
    result = calm_pipeline_check.check()
    assert result["required_doc_count"] == 5
