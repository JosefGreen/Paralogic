from python.paralogic_isft_core import CHECKS, find_countermodel, run_all_checks


def check_by_id(check_id):
    return next(check for check in CHECKS if check.id == check_id)


def test_finite_core_checks_pass():
    results = run_all_checks()
    assert results["ok"]


def test_m8_entails_isf():
    check = check_by_id("EFE-M8-01")
    assert find_countermodel(check) is None


def test_evaluator_acceptance_not_sufficient_for_valid_insight():
    check = check_by_id("EFC-EVAL-02")
    witness = find_countermodel(check)
    assert witness is not None
    assert witness["EvaluatorAccepts"] is True


def test_m8_does_not_imply_harm_or_legal_moral_bridge():
    for check_id in ["EFC-M8-06", "EFC-M8-07", "EFC-M8-08"]:
        witness = find_countermodel(check_by_id(check_id))
        assert witness is not None
