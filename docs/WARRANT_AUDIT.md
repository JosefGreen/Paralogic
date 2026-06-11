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

Latest discharge progress: adequacy now has a scoped operational discharge in
`operationalAdequacyModel`.  In that model, the `adequate` predicate is
computed from an explicit token triple: supported evidence, in-scope context,
and matched claim.  Lean proves the positive adequate case, an unsupported
negative control, and a status refinement
`warrantResolutionStatusWithOperationalAdequacy` that marks adequacy as
`operationallyDischarged` while still proving it is not `sourceBacked` or
`empiricallyValidated`.

Additional discharge progress: evaluator accepting decisions now have a scoped
operational discharge in `operationalEvaluatorModel`.  In that model, the
`evaluatorAccepts` predicate is computed from an approved evaluator/candidate
pair.  Lean connects a satisfied `operationalEvaluatorCriteria` profile and
the existing high-score decision rule to acceptance, while keeping rejected
candidates and low-score acceptance blocked.

Additional discharge progress: contradiction presence now has a scoped
operational discharge in `operationalContradictionModel`.  In that model, the
`contradictionPresent` predicate is computed from the triple active frame,
active context, and contested claim.  Lean proves the positive contested case,
negative controls for resolved claim, inactive frame, and inactive context,
and the profile-to-present conversion.  This remains a scoped operational
rule, not a source-backed or empirically validated theory of every
contradiction kind.

Additional discharge progress: the three M8 power-condition warrants now have
a scoped operational discharge in `operationalPowerModel`.  In that model,
power relevance is computed for a review institution and affected group,
validity dependence is computed for a contested output and material power
condition, and omission is computed for the same material condition.  Lean
also checks negative controls for unaffected group, immaterial condition, and
ordinary output.  This remains local operational semantics, not an externally
validated institutional power analysis.

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
`WarrantObligation` is promoted from `countermodelGuarded` to
`operationallyDischarged`, `sourceBacked`, or `empiricallyValidated` by new
artifacts.  Operational discharge is a formal local semantics, not source or
empirical validation.
