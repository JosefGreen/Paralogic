import Paralogic.ISFTMechanisms

/-!
M5 repair-failure semantics.

M5 is formalized as a local repair-process failure.  The profile records cases
where a repair need is present but planning, action, verification, recurrence
control, and closure boundaries fail while the institution still treats the
output as adequate.
-/

namespace Paralogic

inductive RepairFailureMode where
  | noPlan
  | failedAction
  | unverifiedClosure
  | recurringFailure
  | performativeClosure
  deriving DecidableEq, Repr

structure RepairFailureProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : RepairFailureMode
  repairNeedDeclared : Prop
  responsibleAgentIdentified : Prop
  repairPlanAbsent : Prop
  repairActionFailed : Prop
  verificationAbsent : Prop
  recurrenceMaterial : Prop
  closureClaimMaintained : Prop
  warrantSupportDegraded :
    repairNeedDeclared ->
    responsibleAgentIdentified ->
    repairPlanAbsent ->
    repairActionFailed ->
    verificationAbsent ->
    recurrenceMaterial ->
    closureClaimMaintained ->
    SupportDegradedSem evidence context claim

structure RepairFailureProfileSatisfied {M : SigmaModel}
    (profile : RepairFailureProfile M) : Prop where
  repairNeedDeclared : profile.repairNeedDeclared
  responsibleAgentIdentified : profile.responsibleAgentIdentified
  repairPlanAbsent : profile.repairPlanAbsent
  repairActionFailed : profile.repairActionFailed
  verificationAbsent : profile.verificationAbsent
  recurrenceMaterial : profile.recurrenceMaterial
  closureClaimMaintained : profile.closureClaimMaintained

theorem RepairFailureProfile_to_supportDegraded {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : RepairFailureProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.repairNeedDeclared
    h.responsibleAgentIdentified h.repairPlanAbsent h.repairActionFailed
    h.verificationAbsent h.recurrenceMaterial h.closureClaimMaintained

def RepairFailureProfileBlocked {M : SigmaModel}
    (profile : RepairFailureProfile M) : Prop :=
  Or (Not profile.repairNeedDeclared)
    (Or (Not profile.responsibleAgentIdentified)
      (Or (Not profile.repairPlanAbsent)
        (Or (Not profile.repairActionFailed)
          (Or (Not profile.verificationAbsent)
            (Or (Not profile.recurrenceMaterial)
              (Not profile.closureClaimMaintained))))))

theorem missing_repair_need_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.repairNeedDeclared) :
    RepairFailureProfileBlocked profile :=
  Or.inl h

theorem missing_repair_responsibility_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.responsibleAgentIdentified) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem present_repair_plan_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.repairPlanAbsent) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem successful_repair_action_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.repairActionFailed) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem present_repair_verification_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.verificationAbsent) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem immaterial_recurrence_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.recurrenceMaterial) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem no_repair_closure_claim_blocks_profile {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : Not profile.closureClaimMaintained) :
    RepairFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def RepairFailureProfile.toMechanismProfile {M : SigmaModel}
    (profile : RepairFailureProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M5
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.repairNeedDeclared
    triggerPresent := profile.responsibleAgentIdentified
    claimBasisAvailable := profile.repairPlanAbsent
    supportBasisAvailable := profile.repairActionFailed
    adequacyStandardDeclared := profile.verificationAbsent
    evaluatorBoundaryDeclared := profile.recurrenceMaterial
    nonCollapseBoundaryDeclared := profile.closureClaimMaintained }

theorem RepairFailureProfile_mechanism_label {M : SigmaModel}
    (profile : RepairFailureProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M5 := rfl

theorem RepairFailureProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : RepairFailureProfile M)
    (h : RepairFailureProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.repairNeedDeclared
    trigger := h.responsibleAgentIdentified
    claimBasis := h.repairPlanAbsent
    supportBasis := h.repairActionFailed
    adequacy := h.verificationAbsent
    evaluatorBoundary := h.recurrenceMaterial
    nonCollapseBoundary := h.closureClaimMaintained }

structure M5RepairFailureCase (M : SigmaModel) where
  profile : RepairFailureProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M5RepairFailureSatisfied {M : SigmaModel}
    (caseData : M5RepairFailureCase M) : Prop where
  repairProfileSatisfied :
    RepairFailureProfileSatisfied caseData.profile

theorem M5RepairFailureCase_to_ISFSem {M : SigmaModel}
    (caseData : M5RepairFailureCase M)
    (h : M5RepairFailureSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      RepairFailureProfile_to_supportDegraded caseData.profile
        h.repairProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def repairFailureOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def repairFailureOnlyModel : SigmaModel :=
  UnitPredicateModel repairFailureOnlyTruth

def repairFailureOnlyProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := RepairFailureMode.unverifiedClosure
    repairNeedDeclared := True
    responsibleAgentIdentified := True
    repairPlanAbsent := True
    repairActionFailed := True
    verificationAbsent := True
    recurrenceMaterial := True
    closureClaimMaintained := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem repairFailureOnlyProfile_satisfied :
    RepairFailureProfileSatisfied repairFailureOnlyProfile :=
  { repairNeedDeclared := True.intro
    responsibleAgentIdentified := True.intro
    repairPlanAbsent := True.intro
    repairActionFailed := True.intro
    verificationAbsent := True.intro
    recurrenceMaterial := True.intro
    closureClaimMaintained := True.intro }

def repairFailureNoNeedProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    repairNeedDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def repairFailureNoResponsibilityProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    responsibleAgentIdentified := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def repairFailurePlanPresentProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    repairPlanAbsent := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def repairFailureActionSuccessfulProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    repairActionFailed := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def repairFailureVerifiedProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    verificationAbsent := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def repairFailureNoRecurrenceProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    recurrenceMaterial := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def repairFailureNoClosureClaimProfile :
    RepairFailureProfile repairFailureOnlyModel :=
  { repairFailureOnlyProfile with
    closureClaimMaintained := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem repairFailureNoNeedProfile_blocked :
    RepairFailureProfileBlocked repairFailureNoNeedProfile :=
  missing_repair_need_blocks_profile repairFailureNoNeedProfile
    (by
      intro h
      cases h)

theorem repairFailureNoResponsibilityProfile_blocked :
    RepairFailureProfileBlocked repairFailureNoResponsibilityProfile :=
  missing_repair_responsibility_blocks_profile
    repairFailureNoResponsibilityProfile
    (by
      intro h
      cases h)

theorem repairFailurePlanPresentProfile_blocked :
    RepairFailureProfileBlocked repairFailurePlanPresentProfile :=
  present_repair_plan_blocks_profile repairFailurePlanPresentProfile
    (by
      intro h
      cases h)

theorem repairFailureActionSuccessfulProfile_blocked :
    RepairFailureProfileBlocked repairFailureActionSuccessfulProfile :=
  successful_repair_action_blocks_profile
    repairFailureActionSuccessfulProfile
    (by
      intro h
      cases h)

theorem repairFailureVerifiedProfile_blocked :
    RepairFailureProfileBlocked repairFailureVerifiedProfile :=
  present_repair_verification_blocks_profile repairFailureVerifiedProfile
    (by
      intro h
      cases h)

theorem repairFailureNoRecurrenceProfile_blocked :
    RepairFailureProfileBlocked repairFailureNoRecurrenceProfile :=
  immaterial_recurrence_blocks_profile repairFailureNoRecurrenceProfile
    (by
      intro h
      cases h)

theorem repairFailureNoClosureClaimProfile_blocked :
    RepairFailureProfileBlocked repairFailureNoClosureClaimProfile :=
  no_repair_closure_claim_blocks_profile repairFailureNoClosureClaimProfile
    (by
      intro h
      cases h)

def repairFailureOnlyCase :
    M5RepairFailureCase repairFailureOnlyModel :=
  { profile := repairFailureOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem repairFailureOnlyCase_satisfied :
    M5RepairFailureSatisfied repairFailureOnlyCase :=
  { repairProfileSatisfied := repairFailureOnlyProfile_satisfied }

theorem repairFailureOnly_supportDegraded :
    SupportDegradedSem (M := repairFailureOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  RepairFailureProfile_to_supportDegraded repairFailureOnlyProfile
    repairFailureOnlyProfile_satisfied

theorem repairFailureOnly_to_ISFSem :
    ISFSem repairFailureOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M5RepairFailureCase_to_ISFSem repairFailureOnlyCase
    repairFailureOnlyCase_satisfied

theorem repairFailureOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      repairFailureOnlyProfile.toMechanismProfile :=
  RepairFailureProfile_to_mechanism_satisfied repairFailureOnlyProfile
    repairFailureOnlyProfile_satisfied

end Paralogic
