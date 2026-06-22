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


calm_source_dossier_check = load_module(
    "calm_source_dossier_check", "python/calm_source_dossier_check.py"
)


def test_calm_source_dossier_is_built_and_guarded():
    result = calm_source_dossier_check.check()
    assert result["status"] == "CSD-pass"
    assert result["source_rows"] == 53
    assert result["case_rows"] == 15
    assert result["missing_files"] == []
    assert result["missing_case_packets"] == []
    assert result["forbidden_ready_promotions"] == []
    assert result["audit_has_nonready_verdict"]
    assert result["source_packet_count"] >= 7
