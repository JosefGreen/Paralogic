# Warrant Coverage Check Report

Status: WCC-pass.

This checker parses `src/Paralogic/WarrantDischarge.lean` and verifies that
every constructor of `WarrantObligation` appears as an
`operationallyDischarged` case in `warrantResolutionStatusWithOperationalCore`.
It also checks that the universal Lean coverage theorem and the generic
source-backed / empirical-promotion guard theorems are present.

Scope:

- obligation constructors checked: 11
- operational-core cases checked: 11
- missing operational cases: none
- extra operational cases: none
- required universal theorem names: present

Anti-overclaim guard:

WCC verifies operational warrant coverage only.  It does not establish
source-backed semantics, empirical validation, external legal or moral
authority, real-world reliability statistics, or replication.

Artifacts:

- `python/warrant_coverage_check.py`
- `docs/warrant_coverage_checks/coverage.json`
- `docs/warrant_coverage_checks/obligations.json`
