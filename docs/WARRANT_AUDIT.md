# Warrant Audit

Status: active, with MC3-Lean warrant-discharge scaffold.

Warrants are not derivations merely because they appear as fields in Lean
structures.  This audit separates supplied assumptions from proved results.

| Module | Warrant Field | Current Status | Risk | Required Completion Work |
| --- | --- | --- | --- | --- |
| `Contradiction.lean` | `ContradictionProfile.warrant` | supplied formal field | turns contradiction classification into assumed predicate | define contradiction-detection rules per kind |
| `Adequacy.lean` | `AdequacyProfile.warrant` | supplied formal field | adequacy can be asserted by construction | define domain standards and evidence rules |
| `Evaluator.lean` | `EvaluatorCriteria.warrant` | supplied formal field | acceptance follows from criteria by assumption | define evaluator decision procedure and soundness theorem |
| `Evaluator.lean` | `EvaluatorDecisionCase.acceptsWarrant` | supplied formal field | accepting decisions are not independently checked | connect to scoring and error model |
| `M8Power.lean` | `warrantRelevant`, `warrantDependence`, `warrantOmission` | supplied formal fields | power-erasure conditions may be stipulated | define source-backed power-condition semantics |
| `NormativeBridge.lean` | `NormativeBridgeSchema.warrant` | supplied formal field | normative conclusions can be asserted by bridge construction | externally source/legal-moral-governance standards |
| `EmpiricalValidation.lean` | `EmpiricalValidationProtocol.warrant` | supplied formal field | full validation can be asserted once fields are supplied | require empirical data, reliability, construct validity, replication |
| `ISFTMechanisms.lean` | `SuppressionProfile.warrantSupportDegraded` | supplied formal field | suppression-to-degradation link is assumed | define suppression algebra and evidence rules |
| `Repair.lean` | `RepairDiagnosisProfile.warrantRepairObligation` | supplied formal field | repair obligation follows from supplied warrant | define repair-obligation bridge standards |

Lean discharge layer added: `src/Paralogic/WarrantDischarge.lean`.

The discharge layer enumerates current warrant obligations as:

- `contradictionPresent`
- `adequacy`
- `evaluatorCriteriaAccepts`
- `evaluatorDecisionAccepts`
- `powerRelevant`
- `powerValidityDependence`
- `powerOmitted`
- `normativeBridge`
- `empiricalFullValidation`
- `suppressionSupportDegraded`
- `repairObligation`

Each current obligation is classified as `countermodelGuarded`, not
`sourceBacked` or `empiricallyValidated`.  The module also proves all-false
model countermodels showing that raw profile conditions alone do not force
the warranted conclusions in arbitrary models.

`repairBridgeOnlyTargetedRevision_warrants_obligation` is therefore a
conditional bridge theorem.  The targeted repair action satisfies the local
finite revision postulates, but the repair-obligation conclusion still depends
on the supplied `warrantRepairObligation` field.

## Completion Rule

A warrant-consuming theorem may be MC3-Lean for the conditional statement, but
it does not prove the warrant.  The theorem ledger must not count these as
substantive validation until the warrant source is independently supplied or
derived.

Updated rule: a warrant can now be marked complete only when its
`WarrantObligation` is promoted from `countermodelGuarded` to `sourceBacked`
or `empiricallyValidated` by new artifacts.  Until then, it is accounted for
but not discharged.
