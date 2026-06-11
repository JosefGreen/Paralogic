# M2 Metric Proxy Check Report - 2026-06-11

Status: `M2C-pass`.

This report records the first mechanism-specific deepening pass after the
candidate coverage gate.  M2 is formalized as metric-as-value collapse: a proxy
metric is treated as the target under optimization pressure despite material
proxy-target divergence.

## Checked Artifacts

- Lean source:
  - `src/Paralogic/MetricProxy.lean`
- Executable checker:
  - `python/metric_proxy_check.py`
- Persisted outputs:
  - `docs/metric_proxy_checks/coverage.json`
  - `docs/metric_proxy_checks/conditions.json`

## Formal Surface

The Lean module defines:

- `MetricProxyProfile`;
- `MetricProxyProfileSatisfied`;
- `MetricProxyProfileBlocked`;
- conversion from a satisfied M2 profile to `SupportDegradedSem`;
- conversion from a satisfied M2 profile to a generic `ISFTMechanismProfile`
  labelled `M2`;
- `M2MetricProxyCollapseCase`;
- conversion from a satisfied M2 collapse case to `ISFSem`.

## Required Conditions

The checker confirms all seven required M2 conditions are present in the
profile, satisfaction predicate, and blocked predicate:

- target declared;
- proxy used as target;
- optimization pressure;
- proxy-target divergence;
- material replacement;
- absent boundary guard;
- absent evaluator separation.

## Negative Controls

The Lean module includes one named blocker and one concrete blocked witness for
each required condition.  This prevents the M2 profile from collapsing into a
generic support-degradation claim with no failure-mode discipline.

## Boundary

This pass is not an empirical validation of M2 and is not a source-complete
literature review.  It is a Lean-checked operational profile for the M2
candidate mechanism, with executable coverage checks and explicit blockers.

