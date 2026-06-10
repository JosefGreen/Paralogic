import Paralogic.NormativeBridge

/-!
Repair calculus and bridge independence.

Repair is represented as a staged, condition-gated process.  A repair
diagnosis can warrant a repair-obligation bridge only through an explicit
schema; plans, actions, verification, closure, regress, and externalities are
separate formal objects.  None of these stages implies harm, guilt, valid
insight, or empirical validation without a separate bridge or protocol.
-/

namespace Paralogic

inductive RepairStage where
  | diagnosis
  | plan
  | action
  | verification
  | closure
  | regress
  | externality
  deriving DecidableEq, Repr

inductive RepairRegressKind where
  | recurrence
  | substitution
  | underRepair
  | overRepair
  | proceduralDrift
  deriving DecidableEq, Repr

inductive RepairExternalityKind where
  | burdenShift
  | newExclusion
  | symbolicCover
  | resourceDiversion
  | measurementDistortion
  deriving DecidableEq, Repr

structure RepairDiagnosisProfile (M : SigmaModel) where
  bridge : M.Carrier SortTag.normativeBridge
  institution : M.Carrier SortTag.institution
  group : M.Carrier SortTag.affectedGroup
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  repairNeedIdentified : Prop
  standingDeclared : Prop
  causalPathDeclared : Prop
  scopeBounded : Prop
  affectedGroupConsulted : Prop
  defeatersAbsent : Prop
  warrantRepairObligation :
    repairNeedIdentified ->
    standingDeclared ->
    causalPathDeclared ->
    scopeBounded ->
    affectedGroupConsulted ->
    defeatersAbsent ->
    RepairObligationBridgeSem bridge institution group

structure RepairDiagnosisSatisfied {M : SigmaModel}
    (profile : RepairDiagnosisProfile M) : Prop where
  need : profile.repairNeedIdentified
  standing : profile.standingDeclared
  causalPath : profile.causalPathDeclared
  scope : profile.scopeBounded
  consulted : profile.affectedGroupConsulted
  defeaters : profile.defeatersAbsent

theorem RepairDiagnosisProfile_to_repairObligation {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : RepairDiagnosisSatisfied profile) :
    RepairObligationBridgeSem profile.bridge profile.institution
      profile.group :=
  profile.warrantRepairObligation h.need h.standing h.causalPath h.scope
    h.consulted h.defeaters

def RepairDiagnosisBlocked {M : SigmaModel}
    (profile : RepairDiagnosisProfile M) : Prop :=
  Or (Not profile.repairNeedIdentified)
    (Or (Not profile.standingDeclared)
      (Or (Not profile.causalPathDeclared)
        (Or (Not profile.scopeBounded)
          (Or (Not profile.affectedGroupConsulted)
            (Not profile.defeatersAbsent)))))

theorem missing_repair_need_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.repairNeedIdentified) :
    RepairDiagnosisBlocked profile :=
  Or.inl h

theorem missing_repair_standing_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.standingDeclared) :
    RepairDiagnosisBlocked profile :=
  Or.inr (Or.inl h)

theorem missing_repair_causal_path_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.causalPathDeclared) :
    RepairDiagnosisBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem repair_scope_failure_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.scopeBounded) :
    RepairDiagnosisBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem no_group_consultation_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.affectedGroupConsulted) :
    RepairDiagnosisBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem repair_defeater_blocks_diagnosis {M : SigmaModel}
    (profile : RepairDiagnosisProfile M)
    (h : Not profile.defeatersAbsent) :
    RepairDiagnosisBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

structure RepairPlanProfile (M : SigmaModel) where
  diagnosis : RepairDiagnosisProfile M
  obligation :
    RepairObligationBridgeSem diagnosis.bridge diagnosis.institution
      diagnosis.group
  actionSpecified : Prop
  actorAssigned : Prop
  resourcesAllocated : Prop
  timelineDeclared : Prop
  verificationMetricDeclared : Prop
  nonRecurrenceCriterionDeclared : Prop

structure RepairPlanSatisfied {M : SigmaModel}
    (profile : RepairPlanProfile M) : Prop where
  action : profile.actionSpecified
  actor : profile.actorAssigned
  resources : profile.resourcesAllocated
  timeline : profile.timelineDeclared
  metric : profile.verificationMetricDeclared
  nonRecurrence : profile.nonRecurrenceCriterionDeclared

structure RepairActionProfile (M : SigmaModel) where
  plan : RepairPlanProfile M
  actionPerformed : Prop
  actorMatched : Prop
  resourcesUsedWithinScope : Prop
  timelineRespected : Prop
  deviationsDeclared : Prop

structure RepairActionSatisfied {M : SigmaModel}
    (profile : RepairActionProfile M) : Prop where
  performed : profile.actionPerformed
  actor : profile.actorMatched
  resources : profile.resourcesUsedWithinScope
  timeline : profile.timelineRespected
  deviations : profile.deviationsDeclared

structure RepairVerificationProfile (M : SigmaModel) where
  action : RepairActionProfile M
  metricMeasured : Prop
  affectedGroupFeedbackRecorded : Prop
  independentCheckPerformed : Prop
  residualHarmsAssessed : Prop
  recurrenceAssessed : Prop

structure RepairVerificationSatisfied {M : SigmaModel}
    (profile : RepairVerificationProfile M) : Prop where
  metric : profile.metricMeasured
  feedback : profile.affectedGroupFeedbackRecorded
  independent : profile.independentCheckPerformed
  residual : profile.residualHarmsAssessed
  recurrence : profile.recurrenceAssessed

structure RepairClosureProfile (M : SigmaModel) where
  verification : RepairVerificationProfile M
  verificationSatisfied : RepairVerificationSatisfied verification
  residualExternalitiesAddressed : Prop
  noRegressDetected : Prop
  limitationsDeclared : Prop
  closureScopeBounded : Prop

structure RepairClosureSatisfied {M : SigmaModel}
    (profile : RepairClosureProfile M) : Prop where
  externalities : profile.residualExternalitiesAddressed
  noRegress : profile.noRegressDetected
  limitations : profile.limitationsDeclared
  bounded : profile.closureScopeBounded

structure RepairRegressCase (M : SigmaModel) where
  closure : RepairClosureProfile M
  kind : RepairRegressKind
  recurrenceDetected : Prop
  closureConditionViolated : Prop

def RepairRegressSatisfied {M : SigmaModel}
    (caseData : RepairRegressCase M) : Prop :=
  And caseData.recurrenceDetected caseData.closureConditionViolated

structure RepairExternalityCase (M : SigmaModel) where
  action : RepairActionProfile M
  kind : RepairExternalityKind
  externalityDetected : Prop
  material : Prop
  affectedGroupDifferent : Prop

def RepairExternalitySatisfied {M : SigmaModel}
    (caseData : RepairExternalityCase M) : Prop :=
  And caseData.externalityDetected
    (And caseData.material caseData.affectedGroupDifferent)

def repairBridgeOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.repairObligationBridge => True
  | _ => False

def repairBridgeOnlyModel : SigmaModel :=
  UnitPredicateModel repairBridgeOnlyTruth

def repairBridgeOnlyDiagnosis :
    RepairDiagnosisProfile repairBridgeOnlyModel :=
  { bridge := Unit.unit
    institution := Unit.unit
    group := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    repairNeedIdentified := True
    standingDeclared := True
    causalPathDeclared := True
    scopeBounded := True
    affectedGroupConsulted := True
    defeatersAbsent := True
    warrantRepairObligation := fun _ _ _ _ _ _ => True.intro }

theorem repairBridgeOnlyDiagnosis_satisfied :
    RepairDiagnosisSatisfied repairBridgeOnlyDiagnosis :=
  { need := True.intro
    standing := True.intro
    causalPath := True.intro
    scope := True.intro
    consulted := True.intro
    defeaters := True.intro }

theorem repairBridgeOnly_has_repairObligation :
    RepairObligationBridgeSem (M := repairBridgeOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  RepairDiagnosisProfile_to_repairObligation repairBridgeOnlyDiagnosis
    repairBridgeOnlyDiagnosis_satisfied

def repairBridgeOnlyPlan : RepairPlanProfile repairBridgeOnlyModel :=
  { diagnosis := repairBridgeOnlyDiagnosis
    obligation := repairBridgeOnly_has_repairObligation
    actionSpecified := True
    actorAssigned := True
    resourcesAllocated := True
    timelineDeclared := True
    verificationMetricDeclared := True
    nonRecurrenceCriterionDeclared := True }

theorem repairBridgeOnlyPlan_satisfied :
    RepairPlanSatisfied repairBridgeOnlyPlan :=
  { action := True.intro
    actor := True.intro
    resources := True.intro
    timeline := True.intro
    metric := True.intro
    nonRecurrence := True.intro }

def repairBridgeOnlyAction : RepairActionProfile repairBridgeOnlyModel :=
  { plan := repairBridgeOnlyPlan
    actionPerformed := True
    actorMatched := True
    resourcesUsedWithinScope := True
    timelineRespected := True
    deviationsDeclared := True }

theorem repairBridgeOnlyAction_satisfied :
    RepairActionSatisfied repairBridgeOnlyAction :=
  { performed := True.intro
    actor := True.intro
    resources := True.intro
    timeline := True.intro
    deviations := True.intro }

def repairBridgeOnlyVerification :
    RepairVerificationProfile repairBridgeOnlyModel :=
  { action := repairBridgeOnlyAction
    metricMeasured := True
    affectedGroupFeedbackRecorded := True
    independentCheckPerformed := True
    residualHarmsAssessed := True
    recurrenceAssessed := True }

theorem repairBridgeOnlyVerification_satisfied :
    RepairVerificationSatisfied repairBridgeOnlyVerification :=
  { metric := True.intro
    feedback := True.intro
    independent := True.intro
    residual := True.intro
    recurrence := True.intro }

def repairBridgeOnlyClosure : RepairClosureProfile repairBridgeOnlyModel :=
  { verification := repairBridgeOnlyVerification
    verificationSatisfied := repairBridgeOnlyVerification_satisfied
    residualExternalitiesAddressed := True
    noRegressDetected := True
    limitationsDeclared := True
    closureScopeBounded := True }

theorem repairBridgeOnlyClosure_satisfied :
    RepairClosureSatisfied repairBridgeOnlyClosure :=
  { externalities := True.intro
    noRegress := True.intro
    limitations := True.intro
    bounded := True.intro }

def repairBridgeOnlyRegress : RepairRegressCase repairBridgeOnlyModel :=
  { closure := repairBridgeOnlyClosure
    kind := RepairRegressKind.recurrence
    recurrenceDetected := True
    closureConditionViolated := True }

theorem repairBridgeOnlyRegress_satisfied :
    RepairRegressSatisfied repairBridgeOnlyRegress :=
  And.intro True.intro True.intro

def repairBridgeOnlyExternality :
    RepairExternalityCase repairBridgeOnlyModel :=
  { action := repairBridgeOnlyAction
    kind := RepairExternalityKind.burdenShift
    externalityDetected := True
    material := True
    affectedGroupDifferent := True }

theorem repairBridgeOnlyExternality_satisfied :
    RepairExternalitySatisfied repairBridgeOnlyExternality :=
  And.intro True.intro (And.intro True.intro True.intro)

theorem repairBridgeOnly_not_HarmBridgeSem :
    Not (HarmBridgeSem (M := repairBridgeOnlyModel) Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem repairBridgeOnly_not_MoralGuiltBridgeSem :
    Not (MoralGuiltBridgeSem (M := repairBridgeOnlyModel) Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem repairBridgeOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem repairBridgeOnlyModel Unit.unit
      Unit.unit) := by
  intro h
  exact h.validation

theorem repairBridgeOnly_not_ValidInsightSem :
    Not (ValidInsightSem repairBridgeOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

def harmBridgeOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.harmBridge => True
  | _ => False

def harmBridgeOnlyModel : SigmaModel :=
  UnitPredicateModel harmBridgeOnlyTruth

theorem harmBridgeOnly_has_HarmBridgeSem :
    HarmBridgeSem (M := harmBridgeOnlyModel) Unit.unit Unit.unit Unit.unit :=
  True.intro

theorem harmBridgeOnly_not_RepairObligationBridgeSem :
    Not (RepairObligationBridgeSem (M := harmBridgeOnlyModel) Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h

def defeatedRepairSchema : NormativeBridgeSchema repairBridgeOnlyModel :=
  { conclusion := NormativeConclusion.repairObligation
    bridge := Unit.unit
    institution := Unit.unit
    group := Unit.unit
    premisesSatisfied := True
    scopeApplies := True
    defeatersAbsent := False
    warrant := fun _ _ hdef => False.elim hdef }

theorem defeatedRepairSchema_blocked :
    BridgeDoesNotApply defeatedRepairSchema :=
  defeater_blocks_bridge defeatedRepairSchema (fun h => h)

def repairClosureOnlyTruth (_p : PredicateSymbol) : Prop := False

def repairClosureOnlyModel : SigmaModel :=
  UnitPredicateModel repairClosureOnlyTruth

theorem repairClosureOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem repairClosureOnlyModel Unit.unit
      Unit.unit) := by
  intro h
  exact h.validation

theorem repairClosureOnly_not_MoralGuiltBridgeSem :
    Not (MoralGuiltBridgeSem (M := repairClosureOnlyModel) Unit.unit
      Unit.unit) := by
  intro h
  exact h

end Paralogic
