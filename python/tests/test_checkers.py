from __future__ import annotations

import importlib.util
import json
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


finite_check = load_module("finite_check", "python/finite_check.py")
proof_check = load_module("proof_check", "python/proof_check.py")
granularity_check = load_module("granularity_check", "python/granularity_check.py")
delta_check = load_module("delta_check", "python/delta_check.py")
repair_revision_check = load_module(
    "repair_revision_check", "python/repair_revision_check.py"
)
evaluator_calibration_check = load_module(
    "evaluator_calibration_check", "python/evaluator_calibration_check.py"
)
propositional_proof_check = load_module(
    "propositional_proof_check", "python/propositional_proof_check.py"
)
warrant_coverage_check = load_module(
    "warrant_coverage_check", "python/warrant_coverage_check.py"
)
mechanism_coverage_check = load_module(
    "mechanism_coverage_check", "python/mechanism_coverage_check.py"
)
metric_proxy_check = load_module(
    "metric_proxy_check", "python/metric_proxy_check.py"
)
evidence_overclaim_check = load_module(
    "evidence_overclaim_check", "python/evidence_overclaim_check.py"
)
formal_access_check = load_module(
    "formal_access_check", "python/formal_access_check.py"
)
symbolic_substitution_check = load_module(
    "symbolic_substitution_check", "python/symbolic_substitution_check.py"
)
repair_failure_check = load_module(
    "repair_failure_check", "python/repair_failure_check.py"
)
translation_failure_check = load_module(
    "translation_failure_check", "python/translation_failure_check.py"
)
veto_suppression_check = load_module(
    "veto_suppression_check", "python/veto_suppression_check.py"
)


def test_finite_checker_all_targets_match_expectation():
    failures = []
    for target in finite_check.TARGETS:
        witness, _checked = finite_check.find_counterexample(target)
        found = witness is not None
        if found != target.expects_counterexample:
            failures.append(target.id)
    assert failures == []


def test_finite_checker_records_expected_target_count():
    assert len(finite_check.TARGETS) == 10


def test_finite_checker_positive_targets_have_no_counterexample():
    positive_ids = {
        "EFC-ISF-IMPLIES-USES",
        "EFC-M8-IMPLIES-ISF",
        "EFC-VALID-INSIGHT-IMPLIES-EVAL",
    }
    for target in finite_check.TARGETS:
        if target.id in positive_ids:
            witness, _checked = finite_check.find_counterexample(target)
            assert witness is None


def test_finite_checker_persisted_coverage_matches_targets():
    coverage_path = ROOT / "docs" / "finite_checks" / "coverage.json"
    coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
    target_ids = {target.id for target in finite_check.TARGETS}
    assert {row["id"] for row in coverage} == target_ids
    assert all(row["status"] == "EFC-bounded-pass" for row in coverage)
    for row in coverage:
        expected_count = 2 ** len(row["valuation_scope"])
        assert row["valuation_count"] == expected_count
        assert row["counterexample_found"] == row["expects_counterexample"]
        if row["witness_file"] is not None:
            witness_path = ROOT / "docs" / "finite_checks" / row["witness_file"]
            witness = json.loads(witness_path.read_text(encoding="utf-8"))
            assert witness["id"] == row["id"]
            assert witness["status"] == "EFC-bounded-witness"


def test_proof_checker_all_declared_traces_match_expectation():
    results = [proof_check.check_trace(trace) for trace in proof_check.TRACES]
    assert all(result["passed"] for result in results)


def test_proof_checker_persisted_coverage_matches_traces():
    coverage_path = ROOT / "docs" / "proof_checks" / "coverage.json"
    coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
    assert coverage["status"] == "PYC-pass"
    assert coverage["rule_count"] == len(proof_check.RULES)
    assert coverage["trace_count"] == len(proof_check.TRACES)
    trace_ids = {trace["id"] for trace in proof_check.TRACES}
    assert {result["id"] for result in coverage["results"]} == trace_ids
    for trace_id in trace_ids:
        trace_path = ROOT / "docs" / "proof_checks" / f"{trace_id}.json"
        payload = json.loads(trace_path.read_text(encoding="utf-8"))
        assert payload["trace"]["id"] == trace_id
        assert payload["result"]["passed"]


def test_proof_checker_rejects_unknown_rule():
    trace = {
        "id": "PYC-REJECT-UNKNOWN-RULE",
        "premises": ["ISF"],
        "steps": [
            {"kind": "premise", "atom": "ISF"},
            {"kind": "rule", "rule": "NoSuchRule", "refs": [0], "atom": "Uses"},
        ],
        "expected": "reject",
    }
    result = proof_check.check_trace(trace)
    assert result["status"] == "PYC-reject"
    assert result["passed"]


def test_proof_checker_rejects_invalid_reference():
    trace = {
        "id": "PYC-REJECT-BAD-REF",
        "premises": ["ISF"],
        "steps": [
            {"kind": "premise", "atom": "ISF"},
            {"kind": "rule", "rule": "ISF_to_Uses", "refs": [3], "atom": "Uses"},
        ],
        "expected": "reject",
    }
    result = proof_check.check_trace(trace)
    assert result["status"] == "PYC-reject"
    assert result["passed"]


def test_granularity_checker_refinement_law_has_no_failures():
    rows, failures = granularity_check.check_refinement_law()
    assert len(rows) == 2187
    assert failures == []


def test_granularity_checker_finds_converse_failures():
    witnesses = granularity_check.converse_failures()
    assert witnesses
    assert any(
        witness["item"] == "favorable"
        and witness["fine_lower"]
        and not witness["coarse_lower"]
        for witness in witnesses
    )


def test_granularity_checker_persisted_summary_matches_runtime():
    summary_path = ROOT / "docs" / "granularity_checks" / "summary.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    runtime = granularity_check.summary()
    assert summary == runtime
    assert summary["status"] == "GRC-pass"


def test_granularity_checker_named_lean_witnesses_are_generated():
    named, missing = granularity_check.named_witnesses_are_generated()
    assert missing == []
    assert [row["lean_artifact"] for row in named] == [
        "mask_payload_converse_failure"
    ]


def test_granularity_checker_persisted_named_witnesses_match_runtime():
    path = ROOT / "docs" / "granularity_checks" / "lean_named_witnesses.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == granularity_check.lean_named_witnesses()


def test_delta_checker_named_lean_witnesses_are_supported():
    named, missing = delta_check.named_witnesses_are_supported()
    assert missing == []
    assert [row["lean_artifact"] for row in named] == [
        "eventual_resolution_not_global_finality",
        "stable_resolution_not_global_finality",
        "eventual_stability_not_eventual_resolution",
        "twoDelta_all_states_closed",
        "twoDelta_start_only_not_closed",
        "delta_reachable_closed",
    ]


def test_delta_checker_persisted_summary_matches_runtime():
    path = ROOT / "docs" / "delta_checks" / "summary.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == delta_check.summary()
    assert persisted["status"] == "DLC-pass"


def test_delta_checker_persisted_named_witnesses_match_runtime():
    path = ROOT / "docs" / "delta_checks" / "lean_named_witnesses.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == delta_check.lean_named_witnesses()


def test_delta_checker_closure_records_match_runtime():
    path = ROOT / "docs" / "delta_checks" / "closure_records.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == delta_check.closure_records()
    by_id = {row["id"]: row for row in persisted}
    assert by_id["twoDeltaAllStates"]["closed"]
    assert not by_id["twoDeltaStartOnly"]["closed"]
    assert by_id["twoDeltaReachable"]["closed"]


def test_delta_checker_two_state_sweep_invariants():
    summary = delta_check.two_state_sweep_summary()
    assert summary["status"] == "DLC-two-state-pass"
    assert summary["system_count"] == 64
    assert summary["reachable_not_closed"] == []
    assert summary["always_implies_eventually_failures"] == []
    assert summary["eventual_resolution_not_global_finality_count"] > 0
    assert summary["eventual_stability_not_eventual_resolution_count"] > 0


def test_delta_checker_persisted_two_state_sweep_summary_matches_runtime():
    path = ROOT / "docs" / "delta_checks" / "two_state_sweep_summary.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == delta_check.two_state_sweep_summary()


def test_delta_checker_three_state_sweep_invariants():
    summary = delta_check.three_state_sweep_summary()
    assert summary["status"] == "DLC-three-state-pass"
    assert summary["system_count"] == 4096
    assert summary["reachable_not_closed"] == []
    assert summary["always_implies_eventually_failures"] == []
    assert summary["eventual_resolution_not_global_finality_count"] > 0
    assert summary["eventual_stability_not_eventual_resolution_count"] > 0
    assert summary["stable_resolution_not_global_finality_count"] > 0


def test_delta_checker_persisted_three_state_sweep_summary_matches_runtime():
    path = ROOT / "docs" / "delta_checks" / "three_state_sweep_summary.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == delta_check.three_state_sweep_summary()


def test_repair_revision_checker_named_lean_witnesses_are_supported():
    named, missing = repair_revision_check.named_witnesses_are_supported()
    assert missing == []
    assert [row["lean_artifact"] for row in named] == [
        "rankedRepair_adequate_minimal",
        "rankedRepair_over_not_minimal",
        "rankedRepair_has_unique_minimal",
        "rankedRepair_unique_minimal_from_best",
        "targetedRepair_satisfies_revision_postulates",
        "partialRepair_not_successful",
        "doNothingRepair_not_successful",
        "excessiveRepair_successful_not_minimal",
        "excessiveRepair_not_conservative",
        "excessiveRepair_not_revision_postulates",
        "repairBridgeOnlyTargetedRevision_warrants_obligation",
        "adequateAction_satisfies_independence_package",
        "redundantAction_success_conservative_not_minimal",
        "overreachAction_success_minimal_not_conservative",
        "failedAction_conservative_not_successful",
        "repair revision exhaustive action sweep",
        "repair postulate independence table",
    ]


def test_repair_revision_checker_exhaustive_sweep_invariants():
    summary = repair_revision_check.exhaustive_action_sweep()
    assert summary["status"] == "RRC-pass"
    assert summary["action_map_count"] == 256
    assert summary["action_evaluation_count"] == 1024
    assert summary["minimal_states"] == ["adequate"]
    assert summary["postulate_equivalence_failures"] == []
    assert summary["successful_but_not_postulate_count"] > 0
    assert summary["overrepair_success_not_postulate_count"] > 0


def test_repair_revision_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "repair_revision_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == repair_revision_check.coverage()
    assert persisted["status"] == "RRC-pass"


def test_repair_revision_checker_persisted_sweep_matches_runtime():
    path = ROOT / "docs" / "repair_revision_checks" / "sweep_summary.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == repair_revision_check.exhaustive_action_sweep()


def test_repair_revision_checker_postulate_independence_table():
    summary = repair_revision_check.postulate_independence_summary()
    assert summary["status"] == "RRC-independence-pass"
    assert summary["minimal_states"] == ["adequate", "overreach"]
    rows = {
        row["action"]: row
        for row in repair_revision_check.postulate_independence_table()
    }
    assert rows["adequateAction"]["postulate_package"]
    assert rows["redundantAction"]["success"]
    assert rows["redundantAction"]["conservative"]
    assert not rows["redundantAction"]["minimal"]
    assert rows["overreachAction"]["success"]
    assert rows["overreachAction"]["minimal"]
    assert not rows["overreachAction"]["conservative"]
    assert rows["failedAction"]["conservative"]
    assert not rows["failedAction"]["success"]


def test_repair_revision_checker_persisted_independence_matches_runtime():
    path = (
        ROOT / "docs" / "repair_revision_checks"
        / "postulate_independence_summary.json"
    )
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == repair_revision_check.postulate_independence_summary()


def test_evaluator_calibration_checker_named_lean_witnesses_are_supported():
    named, missing = evaluator_calibration_check.named_witnesses_are_supported()
    assert missing == []
    assert [row["lean_artifact"] for row in named] == [
        "high_score_accepts",
        "medium_score_abstains",
        "low_score_rejects",
        "low_score_not_accepts",
        "medium_score_not_accepts",
        "high_low_scores_disagree",
        "high_medium_scores_disagree",
        "two_high_one_low_majority_accepts",
        "one_high_two_low_majority_rejects",
        "one_high_two_medium_majority_abstains",
        "atLeastTwoAccept_two_high_one_low",
        "not_atLeastTwoAccept_one_high_two_medium",
    ]


def test_evaluator_calibration_checker_exhaustive_triple_summary():
    summary = evaluator_calibration_check.exhaustive_summary()
    assert summary["status"] == "ECC-pass"
    assert summary["triple_count"] == 27
    assert summary["failures"] == []
    assert summary["accept_majority_count"] > 0
    assert summary["reject_majority_count"] > 0
    assert summary["abstain_majority_count"] > 0


def test_evaluator_calibration_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "evaluator_calibration_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == evaluator_calibration_check.coverage()
    assert persisted["status"] == "ECC-pass"


def test_evaluator_calibration_checker_persisted_summary_matches_runtime():
    path = ROOT / "docs" / "evaluator_calibration_checks" / "summary.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == evaluator_calibration_check.exhaustive_summary()


def test_propositional_proof_checker_coverage_matches_targets():
    cov = propositional_proof_check.coverage()
    assert cov["status"] == "PPC-pass"
    assert cov["target_count"] == 7
    assert all(row["passed"] for row in cov["results"])
    by_id = {row["id"]: row for row in cov["results"]}
    assert by_id["PPC-REJECT-AFFIRMING-CONSEQUENT"]["actual"] is False
    assert by_id["PPC-REJECT-DISJUNCTIVE-AFFIRMATION"]["actual"] is False


def test_propositional_proof_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "propositional_proof_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == propositional_proof_check.coverage()


def test_propositional_proof_checker_persisted_targets_exist():
    coverage = propositional_proof_check.coverage()
    for row in coverage["results"]:
        path = (
            ROOT / "docs" / "propositional_proof_checks"
            / f"{row['id']}.json"
        )
        persisted = json.loads(path.read_text(encoding="utf-8"))
        assert persisted == row


def test_warrant_coverage_checker_proves_all_current_obligations_covered():
    coverage = warrant_coverage_check.coverage()
    assert coverage["status"] == "WCC-pass"
    assert coverage["obligation_count"] == 11
    assert coverage["operational_case_count"] == coverage["obligation_count"]
    assert coverage["missing_operational_cases"] == []
    assert coverage["extra_operational_cases"] == []
    assert coverage["missing_theorems"] == []


def test_warrant_coverage_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "warrant_coverage_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == warrant_coverage_check.coverage()


def test_warrant_coverage_checker_persisted_obligations_match_runtime():
    path = ROOT / "docs" / "warrant_coverage_checks" / "obligations.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == warrant_coverage_check.warrant_obligations()


def test_mechanism_coverage_checker_proves_all_current_mechanisms_covered():
    coverage = mechanism_coverage_check.coverage()
    assert coverage["status"] == "MCC-pass"
    assert coverage["mechanism_count"] == 12
    assert coverage["listed_mechanism_count"] == coverage["mechanism_count"]
    assert coverage["duplicate_declared_mechanisms"] == []
    assert coverage["duplicate_listed_mechanisms"] == []
    assert coverage["listed_missing_mechanisms"] == []
    assert coverage["listed_extra_mechanisms"] == []
    assert coverage["mapping_failures"] == {}
    assert coverage["missing_theorems"] == []
    assert coverage["missing_unit_candidate_fields"] == []


def test_mechanism_coverage_checker_mapping_counts_are_exhaustive():
    coverage = mechanism_coverage_check.coverage()
    for row in coverage["mapping_coverage"].values():
        assert row["case_count"] == coverage["mechanism_count"]
        assert row["missing_cases"] == []
        assert row["extra_cases"] == []
        assert row["duplicate_cases"] == []


def test_mechanism_coverage_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "mechanism_coverage_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == mechanism_coverage_check.coverage()


def test_mechanism_coverage_checker_persisted_mechanisms_match_runtime():
    path = ROOT / "docs" / "mechanism_coverage_checks" / "mechanisms.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == mechanism_coverage_check.mechanisms()


def test_metric_proxy_checker_covers_all_m2_conditions():
    coverage = metric_proxy_check.coverage()
    assert coverage["status"] == "M2C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_metric_proxy_checker_has_one_blocker_per_condition():
    coverage = metric_proxy_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_metric_proxy_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "metric_proxy_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == metric_proxy_check.coverage()


def test_metric_proxy_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "metric_proxy_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(metric_proxy_check.REQUIRED_CONDITIONS)


def test_evidence_overclaim_checker_covers_all_m1_conditions():
    coverage = evidence_overclaim_check.coverage()
    assert coverage["status"] == "M1C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_evidence_overclaim_checker_has_one_blocker_per_condition():
    coverage = evidence_overclaim_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_evidence_overclaim_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "evidence_overclaim_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == evidence_overclaim_check.coverage()


def test_evidence_overclaim_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "evidence_overclaim_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(evidence_overclaim_check.REQUIRED_CONDITIONS)


def test_formal_access_checker_covers_all_m3_conditions():
    coverage = formal_access_check.coverage()
    assert coverage["status"] == "M3C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_formal_access_checker_has_one_blocker_per_condition():
    coverage = formal_access_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_formal_access_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "formal_access_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == formal_access_check.coverage()


def test_formal_access_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "formal_access_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(formal_access_check.REQUIRED_CONDITIONS)


def test_symbolic_substitution_checker_covers_all_m4_conditions():
    coverage = symbolic_substitution_check.coverage()
    assert coverage["status"] == "M4C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_symbolic_substitution_checker_has_one_blocker_per_condition():
    coverage = symbolic_substitution_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_symbolic_substitution_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "symbolic_substitution_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == symbolic_substitution_check.coverage()


def test_symbolic_substitution_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "symbolic_substitution_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(symbolic_substitution_check.REQUIRED_CONDITIONS)


def test_repair_failure_checker_covers_all_m5_conditions():
    coverage = repair_failure_check.coverage()
    assert coverage["status"] == "M5C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_repair_failure_checker_has_one_blocker_per_condition():
    coverage = repair_failure_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_repair_failure_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "repair_failure_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == repair_failure_check.coverage()


def test_repair_failure_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "repair_failure_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(repair_failure_check.REQUIRED_CONDITIONS)


def test_translation_failure_checker_covers_all_m6_conditions():
    coverage = translation_failure_check.coverage()
    assert coverage["status"] == "M6C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_translation_failure_checker_has_one_blocker_per_condition():
    coverage = translation_failure_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_translation_failure_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "translation_failure_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == translation_failure_check.coverage()


def test_translation_failure_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "translation_failure_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(translation_failure_check.REQUIRED_CONDITIONS)


def test_veto_suppression_checker_covers_all_m9_conditions():
    coverage = veto_suppression_check.coverage()
    assert coverage["status"] == "M9C-pass"
    assert coverage["condition_count"] == 7
    assert coverage["missing_condition_mentions"] == {}
    assert coverage["missing_positive_artifacts"] == []
    assert coverage["missing_blockers"] == []
    assert coverage["missing_blocked_witnesses"] == []


def test_veto_suppression_checker_has_one_blocker_per_condition():
    coverage = veto_suppression_check.coverage()
    assert coverage["blocker_count"] == coverage["condition_count"]
    assert coverage["blocked_witness_count"] == coverage["condition_count"]
    for places in coverage["conditions"].values():
        assert places == {
            "in_profile": True,
            "in_satisfied": True,
            "in_blocked": True,
        }


def test_veto_suppression_checker_persisted_coverage_matches_runtime():
    path = ROOT / "docs" / "veto_suppression_checks" / "coverage.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == veto_suppression_check.coverage()


def test_veto_suppression_checker_persisted_conditions_match_runtime():
    path = ROOT / "docs" / "veto_suppression_checks" / "conditions.json"
    persisted = json.loads(path.read_text(encoding="utf-8"))
    assert persisted == list(veto_suppression_check.REQUIRED_CONDITIONS)
