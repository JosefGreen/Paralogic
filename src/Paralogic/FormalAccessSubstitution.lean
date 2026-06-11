import Paralogic.ISFTMechanisms

/-!
M3 formal-access substitution semantics.

M3 is formalized as a local access-substitution failure.  The profile records
cases where formal or nominal access is treated as substantive access even
though effective usability, comprehension, agency, remedy, and boundary
conditions are missing.
-/

namespace Paralogic

inductive FormalAccessMode where
  | nominalPermission
  | proceduralAvailability
  | interfaceAvailability
  | noticeProvision
  | channelProvision
  deriving DecidableEq, Repr

structure FormalAccessProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : FormalAccessMode
  formalAccessDeclared : Prop
  substantiveAccessAbsent : Prop
  accessTreatedAsSufficient : Prop
  usabilityBarrierMaterial : Prop
  comprehensionBarrierMaterial : Prop
  remedyPathAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    formalAccessDeclared ->
    substantiveAccessAbsent ->
    accessTreatedAsSufficient ->
    usabilityBarrierMaterial ->
    comprehensionBarrierMaterial ->
    remedyPathAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure FormalAccessProfileSatisfied {M : SigmaModel}
    (profile : FormalAccessProfile M) : Prop where
  formalAccessDeclared : profile.formalAccessDeclared
  substantiveAccessAbsent : profile.substantiveAccessAbsent
  accessTreatedAsSufficient : profile.accessTreatedAsSufficient
  usabilityBarrierMaterial : profile.usabilityBarrierMaterial
  comprehensionBarrierMaterial : profile.comprehensionBarrierMaterial
  remedyPathAbsent : profile.remedyPathAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem FormalAccessProfile_to_supportDegraded {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : FormalAccessProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.formalAccessDeclared
    h.substantiveAccessAbsent h.accessTreatedAsSufficient
    h.usabilityBarrierMaterial h.comprehensionBarrierMaterial
    h.remedyPathAbsent h.boundaryGuardAbsent

def FormalAccessProfileBlocked {M : SigmaModel}
    (profile : FormalAccessProfile M) : Prop :=
  Or (Not profile.formalAccessDeclared)
    (Or (Not profile.substantiveAccessAbsent)
      (Or (Not profile.accessTreatedAsSufficient)
        (Or (Not profile.usabilityBarrierMaterial)
          (Or (Not profile.comprehensionBarrierMaterial)
            (Or (Not profile.remedyPathAbsent)
              (Not profile.boundaryGuardAbsent))))))

theorem missing_formal_access_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.formalAccessDeclared) :
    FormalAccessProfileBlocked profile :=
  Or.inl h

theorem substantive_access_present_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.substantiveAccessAbsent) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem access_not_treated_sufficient_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.accessTreatedAsSufficient) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem immaterial_usability_barrier_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.usabilityBarrierMaterial) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem immaterial_comprehension_barrier_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.comprehensionBarrierMaterial) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem present_remedy_path_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.remedyPathAbsent) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_access_boundary_blocks_profile {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    FormalAccessProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def FormalAccessProfile.toMechanismProfile {M : SigmaModel}
    (profile : FormalAccessProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M3
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.formalAccessDeclared
    triggerPresent := profile.substantiveAccessAbsent
    claimBasisAvailable := profile.accessTreatedAsSufficient
    supportBasisAvailable := profile.usabilityBarrierMaterial
    adequacyStandardDeclared := profile.comprehensionBarrierMaterial
    evaluatorBoundaryDeclared := profile.remedyPathAbsent
    nonCollapseBoundaryDeclared := profile.boundaryGuardAbsent }

theorem FormalAccessProfile_mechanism_label {M : SigmaModel}
    (profile : FormalAccessProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M3 := rfl

theorem FormalAccessProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : FormalAccessProfile M)
    (h : FormalAccessProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.formalAccessDeclared
    trigger := h.substantiveAccessAbsent
    claimBasis := h.accessTreatedAsSufficient
    supportBasis := h.usabilityBarrierMaterial
    adequacy := h.comprehensionBarrierMaterial
    evaluatorBoundary := h.remedyPathAbsent
    nonCollapseBoundary := h.boundaryGuardAbsent }

structure M3FormalAccessSubstitutionCase (M : SigmaModel) where
  profile : FormalAccessProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M3FormalAccessSubstitutionSatisfied {M : SigmaModel}
    (caseData : M3FormalAccessSubstitutionCase M) : Prop where
  accessProfileSatisfied :
    FormalAccessProfileSatisfied caseData.profile

theorem M3FormalAccessSubstitutionCase_to_ISFSem {M : SigmaModel}
    (caseData : M3FormalAccessSubstitutionCase M)
    (h : M3FormalAccessSubstitutionSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      FormalAccessProfile_to_supportDegraded caseData.profile
        h.accessProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def formalAccessOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def formalAccessOnlyModel : SigmaModel :=
  UnitPredicateModel formalAccessOnlyTruth

def formalAccessOnlyProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := FormalAccessMode.proceduralAvailability
    formalAccessDeclared := True
    substantiveAccessAbsent := True
    accessTreatedAsSufficient := True
    usabilityBarrierMaterial := True
    comprehensionBarrierMaterial := True
    remedyPathAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem formalAccessOnlyProfile_satisfied :
    FormalAccessProfileSatisfied formalAccessOnlyProfile :=
  { formalAccessDeclared := True.intro
    substantiveAccessAbsent := True.intro
    accessTreatedAsSufficient := True.intro
    usabilityBarrierMaterial := True.intro
    comprehensionBarrierMaterial := True.intro
    remedyPathAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def formalAccessNoDeclarationProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    formalAccessDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def formalAccessSubstantivePresentProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    substantiveAccessAbsent := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def formalAccessNotSubstitutedProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    accessTreatedAsSufficient := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def formalAccessUsableProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    usabilityBarrierMaterial := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def formalAccessComprehensibleProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    comprehensionBarrierMaterial := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def formalAccessRemedyPresentProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    remedyPathAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def formalAccessBoundaryPresentProfile :
    FormalAccessProfile formalAccessOnlyModel :=
  { formalAccessOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem formalAccessNoDeclarationProfile_blocked :
    FormalAccessProfileBlocked formalAccessNoDeclarationProfile :=
  missing_formal_access_blocks_profile formalAccessNoDeclarationProfile
    (by
      intro h
      cases h)

theorem formalAccessSubstantivePresentProfile_blocked :
    FormalAccessProfileBlocked formalAccessSubstantivePresentProfile :=
  substantive_access_present_blocks_profile
    formalAccessSubstantivePresentProfile
    (by
      intro h
      cases h)

theorem formalAccessNotSubstitutedProfile_blocked :
    FormalAccessProfileBlocked formalAccessNotSubstitutedProfile :=
  access_not_treated_sufficient_blocks_profile
    formalAccessNotSubstitutedProfile
    (by
      intro h
      cases h)

theorem formalAccessUsableProfile_blocked :
    FormalAccessProfileBlocked formalAccessUsableProfile :=
  immaterial_usability_barrier_blocks_profile formalAccessUsableProfile
    (by
      intro h
      cases h)

theorem formalAccessComprehensibleProfile_blocked :
    FormalAccessProfileBlocked formalAccessComprehensibleProfile :=
  immaterial_comprehension_barrier_blocks_profile
    formalAccessComprehensibleProfile
    (by
      intro h
      cases h)

theorem formalAccessRemedyPresentProfile_blocked :
    FormalAccessProfileBlocked formalAccessRemedyPresentProfile :=
  present_remedy_path_blocks_profile formalAccessRemedyPresentProfile
    (by
      intro h
      cases h)

theorem formalAccessBoundaryPresentProfile_blocked :
    FormalAccessProfileBlocked formalAccessBoundaryPresentProfile :=
  present_access_boundary_blocks_profile formalAccessBoundaryPresentProfile
    (by
      intro h
      cases h)

def formalAccessOnlyCase :
    M3FormalAccessSubstitutionCase formalAccessOnlyModel :=
  { profile := formalAccessOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem formalAccessOnlyCase_satisfied :
    M3FormalAccessSubstitutionSatisfied formalAccessOnlyCase :=
  { accessProfileSatisfied := formalAccessOnlyProfile_satisfied }

theorem formalAccessOnly_supportDegraded :
    SupportDegradedSem (M := formalAccessOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  FormalAccessProfile_to_supportDegraded formalAccessOnlyProfile
    formalAccessOnlyProfile_satisfied

theorem formalAccessOnly_to_ISFSem :
    ISFSem formalAccessOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M3FormalAccessSubstitutionCase_to_ISFSem formalAccessOnlyCase
    formalAccessOnlyCase_satisfied

theorem formalAccessOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      formalAccessOnlyProfile.toMechanismProfile :=
  FormalAccessProfile_to_mechanism_satisfied formalAccessOnlyProfile
    formalAccessOnlyProfile_satisfied

end Paralogic
