import Paralogic.ISFTMechanisms

/-!
M2 metric-as-value collapse semantics.

M2 is formalized here as a local proxy-target failure.  The profile does not
claim empirical validation or normative consequences; it only records when a
proxy metric is treated as the target under optimization pressure despite a
material proxy-target divergence.
-/

namespace Paralogic

inductive MetricProxyMode where
  | threshold
  | ranking
  | score
  | quota
  | benchmark
  deriving DecidableEq, Repr

structure MetricProxyProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  proxyMetric : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  targetClaim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : MetricProxyMode
  targetDeclared : Prop
  proxyUsedAsTarget : Prop
  optimizationPressure : Prop
  proxyTargetDivergence : Prop
  replacementMaterial : Prop
  boundaryGuardAbsent : Prop
  evaluatorSeparationAbsent : Prop
  warrantSupportDegraded :
    targetDeclared ->
    proxyUsedAsTarget ->
    optimizationPressure ->
    proxyTargetDivergence ->
    replacementMaterial ->
    boundaryGuardAbsent ->
    evaluatorSeparationAbsent ->
    SupportDegradedSem evidence context claim

structure MetricProxyProfileSatisfied {M : SigmaModel}
    (profile : MetricProxyProfile M) : Prop where
  targetDeclared : profile.targetDeclared
  proxyUsedAsTarget : profile.proxyUsedAsTarget
  optimizationPressure : profile.optimizationPressure
  proxyTargetDivergence : profile.proxyTargetDivergence
  replacementMaterial : profile.replacementMaterial
  boundaryGuardAbsent : profile.boundaryGuardAbsent
  evaluatorSeparationAbsent : profile.evaluatorSeparationAbsent

theorem MetricProxyProfile_to_supportDegraded {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : MetricProxyProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.targetDeclared h.proxyUsedAsTarget
    h.optimizationPressure h.proxyTargetDivergence h.replacementMaterial
    h.boundaryGuardAbsent h.evaluatorSeparationAbsent

def MetricProxyProfileBlocked {M : SigmaModel}
    (profile : MetricProxyProfile M) : Prop :=
  Or (Not profile.targetDeclared)
    (Or (Not profile.proxyUsedAsTarget)
      (Or (Not profile.optimizationPressure)
          (Or (Not profile.proxyTargetDivergence)
            (Or (Not profile.replacementMaterial)
              (Or (Not profile.boundaryGuardAbsent)
                (Not profile.evaluatorSeparationAbsent))))))

theorem missing_metric_target_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.targetDeclared) :
    MetricProxyProfileBlocked profile :=
  Or.inl h

theorem unused_metric_proxy_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.proxyUsedAsTarget) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem absent_metric_pressure_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.optimizationPressure) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem aligned_metric_proxy_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.proxyTargetDivergence) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem immaterial_metric_replacement_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.replacementMaterial) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem guarded_metric_boundary_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem separated_metric_evaluator_blocks_profile {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : Not profile.evaluatorSeparationAbsent) :
    MetricProxyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def MetricProxyProfile.toMechanismProfile {M : SigmaModel}
    (profile : MetricProxyProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M2
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.targetDeclared
    triggerPresent := profile.proxyUsedAsTarget
    claimBasisAvailable := profile.optimizationPressure
    supportBasisAvailable := profile.proxyTargetDivergence
    adequacyStandardDeclared := profile.replacementMaterial
    evaluatorBoundaryDeclared := profile.boundaryGuardAbsent
    nonCollapseBoundaryDeclared := profile.evaluatorSeparationAbsent }

theorem MetricProxyProfile_mechanism_label {M : SigmaModel}
    (profile : MetricProxyProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M2 := rfl

theorem MetricProxyProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : MetricProxyProfile M)
    (h : MetricProxyProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.targetDeclared
    trigger := h.proxyUsedAsTarget
    claimBasis := h.optimizationPressure
    supportBasis := h.proxyTargetDivergence
    adequacy := h.replacementMaterial
    evaluatorBoundary := h.boundaryGuardAbsent
    nonCollapseBoundary := h.evaluatorSeparationAbsent }

structure M2MetricProxyCollapseCase (M : SigmaModel) where
  profile : MetricProxyProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M2MetricProxyCollapseSatisfied {M : SigmaModel}
    (caseData : M2MetricProxyCollapseCase M) : Prop where
  metricProfileSatisfied :
    MetricProxyProfileSatisfied caseData.profile

theorem M2MetricProxyCollapseCase_to_ISFSem {M : SigmaModel}
    (caseData : M2MetricProxyCollapseCase M)
    (h : M2MetricProxyCollapseSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      MetricProxyProfile_to_supportDegraded caseData.profile
        h.metricProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def metricProxyOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def metricProxyOnlyModel : SigmaModel :=
  UnitPredicateModel metricProxyOnlyTruth

def metricProxyOnlyProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    proxyMetric := Unit.unit
    claim := Unit.unit
    targetClaim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := MetricProxyMode.score
    targetDeclared := True
    proxyUsedAsTarget := True
    optimizationPressure := True
    proxyTargetDivergence := True
    replacementMaterial := True
    boundaryGuardAbsent := True
    evaluatorSeparationAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem metricProxyOnlyProfile_satisfied :
    MetricProxyProfileSatisfied metricProxyOnlyProfile :=
  { targetDeclared := True.intro
    proxyUsedAsTarget := True.intro
    optimizationPressure := True.intro
    proxyTargetDivergence := True.intro
    replacementMaterial := True.intro
    boundaryGuardAbsent := True.intro
    evaluatorSeparationAbsent := True.intro }

def metricProxyNoTargetProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    targetDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def metricProxyUnusedProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    proxyUsedAsTarget := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def metricProxyNoPressureProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    optimizationPressure := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def metricProxyAlignedProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    proxyTargetDivergence := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def metricProxyImmaterialProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    replacementMaterial := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def metricProxyGuardedProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def metricProxySeparatedProfile :
    MetricProxyProfile metricProxyOnlyModel :=
  { metricProxyOnlyProfile with
    evaluatorSeparationAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem metricProxyNoTargetProfile_blocked :
    MetricProxyProfileBlocked metricProxyNoTargetProfile :=
  missing_metric_target_blocks_profile metricProxyNoTargetProfile
    (by
      intro h
      cases h)

theorem metricProxyUnusedProfile_blocked :
    MetricProxyProfileBlocked metricProxyUnusedProfile :=
  unused_metric_proxy_blocks_profile metricProxyUnusedProfile
    (by
      intro h
      cases h)

theorem metricProxyNoPressureProfile_blocked :
    MetricProxyProfileBlocked metricProxyNoPressureProfile :=
  absent_metric_pressure_blocks_profile metricProxyNoPressureProfile
    (by
      intro h
      cases h)

theorem metricProxyAlignedProfile_blocked :
    MetricProxyProfileBlocked metricProxyAlignedProfile :=
  aligned_metric_proxy_blocks_profile metricProxyAlignedProfile
    (by
      intro h
      cases h)

theorem metricProxyImmaterialProfile_blocked :
    MetricProxyProfileBlocked metricProxyImmaterialProfile :=
  immaterial_metric_replacement_blocks_profile
    metricProxyImmaterialProfile
    (by
      intro h
      cases h)

theorem metricProxyGuardedProfile_blocked :
    MetricProxyProfileBlocked metricProxyGuardedProfile :=
  guarded_metric_boundary_blocks_profile metricProxyGuardedProfile
    (by
      intro h
      cases h)

theorem metricProxySeparatedProfile_blocked :
    MetricProxyProfileBlocked metricProxySeparatedProfile :=
  separated_metric_evaluator_blocks_profile
    metricProxySeparatedProfile
    (by
      intro h
      cases h)

def metricProxyOnlyCase :
    M2MetricProxyCollapseCase metricProxyOnlyModel :=
  { profile := metricProxyOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem metricProxyOnlyCase_satisfied :
    M2MetricProxyCollapseSatisfied metricProxyOnlyCase :=
  { metricProfileSatisfied := metricProxyOnlyProfile_satisfied }

theorem metricProxyOnly_supportDegraded :
    SupportDegradedSem (M := metricProxyOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  MetricProxyProfile_to_supportDegraded metricProxyOnlyProfile
    metricProxyOnlyProfile_satisfied

theorem metricProxyOnly_to_ISFSem :
    ISFSem metricProxyOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M2MetricProxyCollapseCase_to_ISFSem metricProxyOnlyCase
    metricProxyOnlyCase_satisfied

theorem metricProxyOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      metricProxyOnlyProfile.toMechanismProfile :=
  MetricProxyProfile_to_mechanism_satisfied metricProxyOnlyProfile
    metricProxyOnlyProfile_satisfied

end Paralogic
