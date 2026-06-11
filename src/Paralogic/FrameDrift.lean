import Paralogic.ISFTMechanisms

/-!
M10 frame-drift semantics.

M10 is formalized as a local frame/context failure.  The profile records cases
where a claim is carried from a declared source frame to a target frame while
material context conditions have changed and continuity controls are missing.
-/

namespace Paralogic

inductive FrameDriftMode where
  | contextMigration
  | audienceShift
  | temporalCarryover
  | jurisdictionalTransfer
  | scaleShift
  deriving DecidableEq, Repr

structure FrameDriftProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  sourceFrame : M.Carrier SortTag.frame
  targetFrame : M.Carrier SortTag.frame
  mode : FrameDriftMode
  sourceFrameDeclared : Prop
  targetFrameUsed : Prop
  frameShiftPresent : Prop
  claimCarriedAcrossFrames : Prop
  contextConditionsChanged : Prop
  driftMaterial : Prop
  continuityGuardAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    sourceFrameDeclared ->
    targetFrameUsed ->
    frameShiftPresent ->
    claimCarriedAcrossFrames ->
    contextConditionsChanged ->
    driftMaterial ->
    continuityGuardAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure FrameDriftProfileSatisfied {M : SigmaModel}
    (profile : FrameDriftProfile M) : Prop where
  sourceFrameDeclared : profile.sourceFrameDeclared
  targetFrameUsed : profile.targetFrameUsed
  frameShiftPresent : profile.frameShiftPresent
  claimCarriedAcrossFrames : profile.claimCarriedAcrossFrames
  contextConditionsChanged : profile.contextConditionsChanged
  driftMaterial : profile.driftMaterial
  continuityGuardAbsent : profile.continuityGuardAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem FrameDriftProfile_to_supportDegraded {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : FrameDriftProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.sourceFrameDeclared h.targetFrameUsed
    h.frameShiftPresent h.claimCarriedAcrossFrames
    h.contextConditionsChanged h.driftMaterial h.continuityGuardAbsent
    h.boundaryGuardAbsent

def FrameDriftProfileBlocked {M : SigmaModel}
    (profile : FrameDriftProfile M) : Prop :=
  Or (Not profile.sourceFrameDeclared)
    (Or (Not profile.targetFrameUsed)
      (Or (Not profile.frameShiftPresent)
        (Or (Not profile.claimCarriedAcrossFrames)
          (Or (Not profile.contextConditionsChanged)
            (Or (Not profile.driftMaterial)
              (Or (Not profile.continuityGuardAbsent)
                (Not profile.boundaryGuardAbsent)))))))

theorem missing_source_frame_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.sourceFrameDeclared) :
    FrameDriftProfileBlocked profile :=
  Or.inl h

theorem missing_target_frame_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.targetFrameUsed) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem missing_frame_shift_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.frameShiftPresent) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem missing_frame_carry_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.claimCarriedAcrossFrames) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem unchanged_context_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.contextConditionsChanged) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem immaterial_frame_drift_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.driftMaterial) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_continuity_guard_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.continuityGuardAbsent) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem present_frame_boundary_blocks_profile {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    FrameDriftProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

def FrameDriftProfile.toMechanismProfile {M : SigmaModel}
    (profile : FrameDriftProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M10
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.sourceFrameDeclared
    triggerPresent := profile.targetFrameUsed
    claimBasisAvailable := profile.frameShiftPresent
    supportBasisAvailable := profile.claimCarriedAcrossFrames
    adequacyStandardDeclared := profile.contextConditionsChanged
    evaluatorBoundaryDeclared := profile.driftMaterial
    nonCollapseBoundaryDeclared :=
      And profile.continuityGuardAbsent profile.boundaryGuardAbsent }

theorem FrameDriftProfile_mechanism_label {M : SigmaModel}
    (profile : FrameDriftProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M10 := rfl

theorem FrameDriftProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : FrameDriftProfile M)
    (h : FrameDriftProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.sourceFrameDeclared
    trigger := h.targetFrameUsed
    claimBasis := h.frameShiftPresent
    supportBasis := h.claimCarriedAcrossFrames
    adequacy := h.contextConditionsChanged
    evaluatorBoundary := h.driftMaterial
    nonCollapseBoundary :=
      And.intro h.continuityGuardAbsent h.boundaryGuardAbsent }

structure M10FrameDriftCase (M : SigmaModel) where
  profile : FrameDriftProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context
  directionalNonEquivalence :
    DirectionalNonEquivalenceSem profile.sourceFrame profile.targetFrame

structure M10FrameDriftSatisfied {M : SigmaModel}
    (caseData : M10FrameDriftCase M) : Prop where
  driftProfileSatisfied : FrameDriftProfileSatisfied caseData.profile

theorem M10FrameDriftCase_to_ISFSem {M : SigmaModel}
    (caseData : M10FrameDriftCase M)
    (h : M10FrameDriftSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      FrameDriftProfile_to_supportDegraded caseData.profile
        h.driftProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

theorem M10FrameDriftCase_directional_change {M : SigmaModel}
    (caseData : M10FrameDriftCase M) :
    DirectionalNonEquivalenceSem caseData.profile.sourceFrame
      caseData.profile.targetFrame :=
  caseData.directionalNonEquivalence

def frameDriftOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | PredicateSymbol.directionalNonEquivalence => True
  | _ => False

def frameDriftOnlyModel : SigmaModel :=
  UnitPredicateModel frameDriftOnlyTruth

def frameDriftOnlyProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    sourceFrame := Unit.unit
    targetFrame := Unit.unit
    mode := FrameDriftMode.contextMigration
    sourceFrameDeclared := True
    targetFrameUsed := True
    frameShiftPresent := True
    claimCarriedAcrossFrames := True
    contextConditionsChanged := True
    driftMaterial := True
    continuityGuardAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ _ => True.intro }

theorem frameDriftOnlyProfile_satisfied :
    FrameDriftProfileSatisfied frameDriftOnlyProfile :=
  { sourceFrameDeclared := True.intro
    targetFrameUsed := True.intro
    frameShiftPresent := True.intro
    claimCarriedAcrossFrames := True.intro
    contextConditionsChanged := True.intro
    driftMaterial := True.intro
    continuityGuardAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def frameDriftNoSourceProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    sourceFrameDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ _ => False.elim h }

def frameDriftNoTargetProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    targetFrameUsed := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ _ => False.elim h }

def frameDriftNoShiftProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    frameShiftPresent := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ _ => False.elim h }

def frameDriftNoCarryProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    claimCarriedAcrossFrames := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ _ => False.elim h }

def frameDriftUnchangedContextProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    contextConditionsChanged := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ _ => False.elim h }

def frameDriftImmaterialProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    driftMaterial := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ _ => False.elim h }

def frameDriftContinuityPresentProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    continuityGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h _ => False.elim h }

def frameDriftBoundaryPresentProfile :
    FrameDriftProfile frameDriftOnlyModel :=
  { frameDriftOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ _ h => False.elim h }

theorem frameDriftNoSourceProfile_blocked :
    FrameDriftProfileBlocked frameDriftNoSourceProfile :=
  missing_source_frame_blocks_profile frameDriftNoSourceProfile
    (by
      intro h
      cases h)

theorem frameDriftNoTargetProfile_blocked :
    FrameDriftProfileBlocked frameDriftNoTargetProfile :=
  missing_target_frame_blocks_profile frameDriftNoTargetProfile
    (by
      intro h
      cases h)

theorem frameDriftNoShiftProfile_blocked :
    FrameDriftProfileBlocked frameDriftNoShiftProfile :=
  missing_frame_shift_blocks_profile frameDriftNoShiftProfile
    (by
      intro h
      cases h)

theorem frameDriftNoCarryProfile_blocked :
    FrameDriftProfileBlocked frameDriftNoCarryProfile :=
  missing_frame_carry_blocks_profile frameDriftNoCarryProfile
    (by
      intro h
      cases h)

theorem frameDriftUnchangedContextProfile_blocked :
    FrameDriftProfileBlocked frameDriftUnchangedContextProfile :=
  unchanged_context_blocks_profile frameDriftUnchangedContextProfile
    (by
      intro h
      cases h)

theorem frameDriftImmaterialProfile_blocked :
    FrameDriftProfileBlocked frameDriftImmaterialProfile :=
  immaterial_frame_drift_blocks_profile frameDriftImmaterialProfile
    (by
      intro h
      cases h)

theorem frameDriftContinuityPresentProfile_blocked :
    FrameDriftProfileBlocked frameDriftContinuityPresentProfile :=
  present_continuity_guard_blocks_profile
    frameDriftContinuityPresentProfile
    (by
      intro h
      cases h)

theorem frameDriftBoundaryPresentProfile_blocked :
    FrameDriftProfileBlocked frameDriftBoundaryPresentProfile :=
  present_frame_boundary_blocks_profile frameDriftBoundaryPresentProfile
    (by
      intro h
      cases h)

def frameDriftOnlyCase :
    M10FrameDriftCase frameDriftOnlyModel :=
  { profile := frameDriftOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro
    directionalNonEquivalence := True.intro }

theorem frameDriftOnlyCase_satisfied :
    M10FrameDriftSatisfied frameDriftOnlyCase :=
  { driftProfileSatisfied := frameDriftOnlyProfile_satisfied }

theorem frameDriftOnly_supportDegraded :
    SupportDegradedSem (M := frameDriftOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  FrameDriftProfile_to_supportDegraded frameDriftOnlyProfile
    frameDriftOnlyProfile_satisfied

theorem frameDriftOnly_to_ISFSem :
    ISFSem frameDriftOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M10FrameDriftCase_to_ISFSem frameDriftOnlyCase
    frameDriftOnlyCase_satisfied

theorem frameDriftOnly_directional_change :
    DirectionalNonEquivalenceSem (M := frameDriftOnlyModel) Unit.unit
      Unit.unit :=
  M10FrameDriftCase_directional_change frameDriftOnlyCase

theorem frameDriftOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      frameDriftOnlyProfile.toMechanismProfile :=
  FrameDriftProfile_to_mechanism_satisfied frameDriftOnlyProfile
    frameDriftOnlyProfile_satisfied

end Paralogic
