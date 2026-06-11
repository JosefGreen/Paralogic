import Paralogic.ISFTMechanisms

/-!
M1 evidence-overclaim semantics.

M1 is formalized as a local claim-support failure.  The profile records cases
where an institution treats a claim as adequately supported even though the
available evidence is relevant but insufficient, scope-mismatched, uncertainty
exposed, and materially overextended.
-/

namespace Paralogic

inductive EvidenceOverclaimMode where
  | scopeExpansion
  | certaintyInflation
  | sampleOverreach
  | causalOverreach
  | temporalOverreach
  deriving DecidableEq, Repr

structure EvidenceOverclaimProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : EvidenceOverclaimMode
  claimScopeDeclared : Prop
  evidenceRelevant : Prop
  evidenceInsufficient : Prop
  scopeMismatch : Prop
  uncertaintyUnbounded : Prop
  overclaimMaterial : Prop
  adequacyBoundaryAbsent : Prop
  warrantSupportDegraded :
    claimScopeDeclared ->
    evidenceRelevant ->
    evidenceInsufficient ->
    scopeMismatch ->
    uncertaintyUnbounded ->
    overclaimMaterial ->
    adequacyBoundaryAbsent ->
    SupportDegradedSem evidence context claim

structure EvidenceOverclaimProfileSatisfied {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M) : Prop where
  claimScopeDeclared : profile.claimScopeDeclared
  evidenceRelevant : profile.evidenceRelevant
  evidenceInsufficient : profile.evidenceInsufficient
  scopeMismatch : profile.scopeMismatch
  uncertaintyUnbounded : profile.uncertaintyUnbounded
  overclaimMaterial : profile.overclaimMaterial
  adequacyBoundaryAbsent : profile.adequacyBoundaryAbsent

theorem EvidenceOverclaimProfile_to_supportDegraded {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : EvidenceOverclaimProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.claimScopeDeclared h.evidenceRelevant
    h.evidenceInsufficient h.scopeMismatch h.uncertaintyUnbounded
    h.overclaimMaterial h.adequacyBoundaryAbsent

def EvidenceOverclaimProfileBlocked {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M) : Prop :=
  Or (Not profile.claimScopeDeclared)
    (Or (Not profile.evidenceRelevant)
      (Or (Not profile.evidenceInsufficient)
        (Or (Not profile.scopeMismatch)
          (Or (Not profile.uncertaintyUnbounded)
            (Or (Not profile.overclaimMaterial)
              (Not profile.adequacyBoundaryAbsent))))))

theorem missing_claim_scope_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.claimScopeDeclared) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inl h

theorem irrelevant_evidence_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.evidenceRelevant) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem sufficient_evidence_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.evidenceInsufficient) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem matched_scope_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.scopeMismatch) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem bounded_uncertainty_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.uncertaintyUnbounded) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem immaterial_overclaim_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.overclaimMaterial) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_adequacy_boundary_blocks_overclaim {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : Not profile.adequacyBoundaryAbsent) :
    EvidenceOverclaimProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def EvidenceOverclaimProfile.toMechanismProfile {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M1
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.claimScopeDeclared
    triggerPresent := profile.evidenceRelevant
    claimBasisAvailable := profile.evidenceInsufficient
    supportBasisAvailable := profile.scopeMismatch
    adequacyStandardDeclared := profile.uncertaintyUnbounded
    evaluatorBoundaryDeclared := profile.overclaimMaterial
    nonCollapseBoundaryDeclared := profile.adequacyBoundaryAbsent }

theorem EvidenceOverclaimProfile_mechanism_label {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M1 := rfl

theorem EvidenceOverclaimProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : EvidenceOverclaimProfile M)
    (h : EvidenceOverclaimProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.claimScopeDeclared
    trigger := h.evidenceRelevant
    claimBasis := h.evidenceInsufficient
    supportBasis := h.scopeMismatch
    adequacy := h.uncertaintyUnbounded
    evaluatorBoundary := h.overclaimMaterial
    nonCollapseBoundary := h.adequacyBoundaryAbsent }

structure M1EvidenceOverclaimCase (M : SigmaModel) where
  profile : EvidenceOverclaimProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M1EvidenceOverclaimSatisfied {M : SigmaModel}
    (caseData : M1EvidenceOverclaimCase M) : Prop where
  evidenceProfileSatisfied :
    EvidenceOverclaimProfileSatisfied caseData.profile

theorem M1EvidenceOverclaimCase_to_ISFSem {M : SigmaModel}
    (caseData : M1EvidenceOverclaimCase M)
    (h : M1EvidenceOverclaimSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      EvidenceOverclaimProfile_to_supportDegraded caseData.profile
        h.evidenceProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def evidenceOverclaimOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def evidenceOverclaimOnlyModel : SigmaModel :=
  UnitPredicateModel evidenceOverclaimOnlyTruth

def evidenceOverclaimOnlyProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := EvidenceOverclaimMode.scopeExpansion
    claimScopeDeclared := True
    evidenceRelevant := True
    evidenceInsufficient := True
    scopeMismatch := True
    uncertaintyUnbounded := True
    overclaimMaterial := True
    adequacyBoundaryAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem evidenceOverclaimOnlyProfile_satisfied :
    EvidenceOverclaimProfileSatisfied evidenceOverclaimOnlyProfile :=
  { claimScopeDeclared := True.intro
    evidenceRelevant := True.intro
    evidenceInsufficient := True.intro
    scopeMismatch := True.intro
    uncertaintyUnbounded := True.intro
    overclaimMaterial := True.intro
    adequacyBoundaryAbsent := True.intro }

def evidenceOverclaimNoScopeProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    claimScopeDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def evidenceOverclaimIrrelevantProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    evidenceRelevant := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def evidenceOverclaimSufficientProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    evidenceInsufficient := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def evidenceOverclaimMatchedScopeProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    scopeMismatch := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def evidenceOverclaimBoundedUncertaintyProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    uncertaintyUnbounded := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def evidenceOverclaimImmaterialProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    overclaimMaterial := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def evidenceOverclaimBoundaryPresentProfile :
    EvidenceOverclaimProfile evidenceOverclaimOnlyModel :=
  { evidenceOverclaimOnlyProfile with
    adequacyBoundaryAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem evidenceOverclaimNoScopeProfile_blocked :
    EvidenceOverclaimProfileBlocked evidenceOverclaimNoScopeProfile :=
  missing_claim_scope_blocks_overclaim evidenceOverclaimNoScopeProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimIrrelevantProfile_blocked :
    EvidenceOverclaimProfileBlocked evidenceOverclaimIrrelevantProfile :=
  irrelevant_evidence_blocks_overclaim evidenceOverclaimIrrelevantProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimSufficientProfile_blocked :
    EvidenceOverclaimProfileBlocked evidenceOverclaimSufficientProfile :=
  sufficient_evidence_blocks_overclaim evidenceOverclaimSufficientProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimMatchedScopeProfile_blocked :
    EvidenceOverclaimProfileBlocked evidenceOverclaimMatchedScopeProfile :=
  matched_scope_blocks_overclaim evidenceOverclaimMatchedScopeProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimBoundedUncertaintyProfile_blocked :
    EvidenceOverclaimProfileBlocked
      evidenceOverclaimBoundedUncertaintyProfile :=
  bounded_uncertainty_blocks_overclaim
    evidenceOverclaimBoundedUncertaintyProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimImmaterialProfile_blocked :
    EvidenceOverclaimProfileBlocked evidenceOverclaimImmaterialProfile :=
  immaterial_overclaim_blocks_overclaim evidenceOverclaimImmaterialProfile
    (by
      intro h
      cases h)

theorem evidenceOverclaimBoundaryPresentProfile_blocked :
    EvidenceOverclaimProfileBlocked
      evidenceOverclaimBoundaryPresentProfile :=
  present_adequacy_boundary_blocks_overclaim
    evidenceOverclaimBoundaryPresentProfile
    (by
      intro h
      cases h)

def evidenceOverclaimOnlyCase :
    M1EvidenceOverclaimCase evidenceOverclaimOnlyModel :=
  { profile := evidenceOverclaimOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem evidenceOverclaimOnlyCase_satisfied :
    M1EvidenceOverclaimSatisfied evidenceOverclaimOnlyCase :=
  { evidenceProfileSatisfied := evidenceOverclaimOnlyProfile_satisfied }

theorem evidenceOverclaimOnly_supportDegraded :
    SupportDegradedSem (M := evidenceOverclaimOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  EvidenceOverclaimProfile_to_supportDegraded evidenceOverclaimOnlyProfile
    evidenceOverclaimOnlyProfile_satisfied

theorem evidenceOverclaimOnly_to_ISFSem :
    ISFSem evidenceOverclaimOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M1EvidenceOverclaimCase_to_ISFSem evidenceOverclaimOnlyCase
    evidenceOverclaimOnlyCase_satisfied

theorem evidenceOverclaimOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      evidenceOverclaimOnlyProfile.toMechanismProfile :=
  EvidenceOverclaimProfile_to_mechanism_satisfied
    evidenceOverclaimOnlyProfile
    evidenceOverclaimOnlyProfile_satisfied

end Paralogic
