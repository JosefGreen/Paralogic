import Paralogic.ISFTMechanisms

/-!
M9 veto-suppression semantics.

M9 is formalized as a local participation failure.  The profile records cases
where a veto or blocking right is declared or procedurally available, but an
attempted veto is suppressed while review and boundary conditions are missing.
-/

namespace Paralogic

inductive VetoSuppressionMode where
  | proceduralBypass
  | agendaControl
  | timingClosure
  | thresholdManipulation
  | participationMasking
  deriving DecidableEq, Repr

structure VetoSuppressionProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : VetoSuppressionMode
  vetoRightDeclared : Prop
  affectedParticipantPresent : Prop
  vetoAttemptMade : Prop
  vetoSuppressed : Prop
  suppressionMaterial : Prop
  reviewPathAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    vetoRightDeclared ->
    affectedParticipantPresent ->
    vetoAttemptMade ->
    vetoSuppressed ->
    suppressionMaterial ->
    reviewPathAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure VetoSuppressionProfileSatisfied {M : SigmaModel}
    (profile : VetoSuppressionProfile M) : Prop where
  vetoRightDeclared : profile.vetoRightDeclared
  affectedParticipantPresent : profile.affectedParticipantPresent
  vetoAttemptMade : profile.vetoAttemptMade
  vetoSuppressed : profile.vetoSuppressed
  suppressionMaterial : profile.suppressionMaterial
  reviewPathAbsent : profile.reviewPathAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem VetoSuppressionProfile_to_supportDegraded {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : VetoSuppressionProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.vetoRightDeclared
    h.affectedParticipantPresent h.vetoAttemptMade h.vetoSuppressed
    h.suppressionMaterial h.reviewPathAbsent h.boundaryGuardAbsent

def VetoSuppressionProfileBlocked {M : SigmaModel}
    (profile : VetoSuppressionProfile M) : Prop :=
  Or (Not profile.vetoRightDeclared)
    (Or (Not profile.affectedParticipantPresent)
      (Or (Not profile.vetoAttemptMade)
        (Or (Not profile.vetoSuppressed)
          (Or (Not profile.suppressionMaterial)
            (Or (Not profile.reviewPathAbsent)
              (Not profile.boundaryGuardAbsent))))))

theorem missing_veto_right_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.vetoRightDeclared) :
    VetoSuppressionProfileBlocked profile :=
  Or.inl h

theorem missing_affected_participant_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.affectedParticipantPresent) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem absent_veto_attempt_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.vetoAttemptMade) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem unsuppressed_veto_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.vetoSuppressed) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem immaterial_veto_suppression_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.suppressionMaterial) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem present_veto_review_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.reviewPathAbsent) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_veto_boundary_blocks_profile {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    VetoSuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def VetoSuppressionProfile.toMechanismProfile {M : SigmaModel}
    (profile : VetoSuppressionProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M9
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.vetoRightDeclared
    triggerPresent := profile.affectedParticipantPresent
    claimBasisAvailable := profile.vetoAttemptMade
    supportBasisAvailable := profile.vetoSuppressed
    adequacyStandardDeclared := profile.suppressionMaterial
    evaluatorBoundaryDeclared := profile.reviewPathAbsent
    nonCollapseBoundaryDeclared := profile.boundaryGuardAbsent }

theorem VetoSuppressionProfile_mechanism_label {M : SigmaModel}
    (profile : VetoSuppressionProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M9 := rfl

theorem VetoSuppressionProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : VetoSuppressionProfile M)
    (h : VetoSuppressionProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.vetoRightDeclared
    trigger := h.affectedParticipantPresent
    claimBasis := h.vetoAttemptMade
    supportBasis := h.vetoSuppressed
    adequacy := h.suppressionMaterial
    evaluatorBoundary := h.reviewPathAbsent
    nonCollapseBoundary := h.boundaryGuardAbsent }

structure M9VetoSuppressionCase (M : SigmaModel) where
  profile : VetoSuppressionProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M9VetoSuppressionSatisfied {M : SigmaModel}
    (caseData : M9VetoSuppressionCase M) : Prop where
  vetoProfileSatisfied :
    VetoSuppressionProfileSatisfied caseData.profile

theorem M9VetoSuppressionCase_to_ISFSem {M : SigmaModel}
    (caseData : M9VetoSuppressionCase M)
    (h : M9VetoSuppressionSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      VetoSuppressionProfile_to_supportDegraded caseData.profile
        h.vetoProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def vetoSuppressionOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def vetoSuppressionOnlyModel : SigmaModel :=
  UnitPredicateModel vetoSuppressionOnlyTruth

def vetoSuppressionOnlyProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := VetoSuppressionMode.proceduralBypass
    vetoRightDeclared := True
    affectedParticipantPresent := True
    vetoAttemptMade := True
    vetoSuppressed := True
    suppressionMaterial := True
    reviewPathAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem vetoSuppressionOnlyProfile_satisfied :
    VetoSuppressionProfileSatisfied vetoSuppressionOnlyProfile :=
  { vetoRightDeclared := True.intro
    affectedParticipantPresent := True.intro
    vetoAttemptMade := True.intro
    vetoSuppressed := True.intro
    suppressionMaterial := True.intro
    reviewPathAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def vetoSuppressionNoRightProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    vetoRightDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def vetoSuppressionNoParticipantProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    affectedParticipantPresent := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def vetoSuppressionNoAttemptProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    vetoAttemptMade := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def vetoSuppressionNotSuppressedProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    vetoSuppressed := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def vetoSuppressionImmaterialProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    suppressionMaterial := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def vetoSuppressionReviewPresentProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    reviewPathAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def vetoSuppressionBoundaryPresentProfile :
    VetoSuppressionProfile vetoSuppressionOnlyModel :=
  { vetoSuppressionOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem vetoSuppressionNoRightProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionNoRightProfile :=
  missing_veto_right_blocks_profile vetoSuppressionNoRightProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionNoParticipantProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionNoParticipantProfile :=
  missing_affected_participant_blocks_profile
    vetoSuppressionNoParticipantProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionNoAttemptProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionNoAttemptProfile :=
  absent_veto_attempt_blocks_profile vetoSuppressionNoAttemptProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionNotSuppressedProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionNotSuppressedProfile :=
  unsuppressed_veto_blocks_profile vetoSuppressionNotSuppressedProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionImmaterialProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionImmaterialProfile :=
  immaterial_veto_suppression_blocks_profile
    vetoSuppressionImmaterialProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionReviewPresentProfile_blocked :
    VetoSuppressionProfileBlocked vetoSuppressionReviewPresentProfile :=
  present_veto_review_blocks_profile vetoSuppressionReviewPresentProfile
    (by
      intro h
      cases h)

theorem vetoSuppressionBoundaryPresentProfile_blocked :
    VetoSuppressionProfileBlocked
      vetoSuppressionBoundaryPresentProfile :=
  present_veto_boundary_blocks_profile
    vetoSuppressionBoundaryPresentProfile
    (by
      intro h
      cases h)

def vetoSuppressionOnlyCase :
    M9VetoSuppressionCase vetoSuppressionOnlyModel :=
  { profile := vetoSuppressionOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem vetoSuppressionOnlyCase_satisfied :
    M9VetoSuppressionSatisfied vetoSuppressionOnlyCase :=
  { vetoProfileSatisfied := vetoSuppressionOnlyProfile_satisfied }

theorem vetoSuppressionOnly_supportDegraded :
    SupportDegradedSem (M := vetoSuppressionOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  VetoSuppressionProfile_to_supportDegraded vetoSuppressionOnlyProfile
    vetoSuppressionOnlyProfile_satisfied

theorem vetoSuppressionOnly_to_ISFSem :
    ISFSem vetoSuppressionOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M9VetoSuppressionCase_to_ISFSem vetoSuppressionOnlyCase
    vetoSuppressionOnlyCase_satisfied

theorem vetoSuppressionOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      vetoSuppressionOnlyProfile.toMechanismProfile :=
  VetoSuppressionProfile_to_mechanism_satisfied vetoSuppressionOnlyProfile
    vetoSuppressionOnlyProfile_satisfied

end Paralogic
