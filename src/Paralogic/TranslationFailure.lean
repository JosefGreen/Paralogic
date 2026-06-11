import Paralogic.ISFTMechanisms

/-!
M6 translation-failure semantics.

M6 is formalized as a local translation-network failure.  The profile records
cases where a translation between source and target contexts is treated as
adequate even though semantic loss, broken linkage, missing verification, and
boundary failure degrade support.
-/

namespace Paralogic

inductive TranslationFailureMode where
  | semanticLoss
  | contextLoss
  | actorLinkBreak
  | channelMismatch
  | verificationGap
  deriving DecidableEq, Repr

structure TranslationFailureProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : TranslationFailureMode
  sourceContextDeclared : Prop
  targetContextDeclared : Prop
  translationPerformed : Prop
  semanticLossMaterial : Prop
  actorLinkBroken : Prop
  verificationAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    sourceContextDeclared ->
    targetContextDeclared ->
    translationPerformed ->
    semanticLossMaterial ->
    actorLinkBroken ->
    verificationAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure TranslationFailureProfileSatisfied {M : SigmaModel}
    (profile : TranslationFailureProfile M) : Prop where
  sourceContextDeclared : profile.sourceContextDeclared
  targetContextDeclared : profile.targetContextDeclared
  translationPerformed : profile.translationPerformed
  semanticLossMaterial : profile.semanticLossMaterial
  actorLinkBroken : profile.actorLinkBroken
  verificationAbsent : profile.verificationAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem TranslationFailureProfile_to_supportDegraded {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : TranslationFailureProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.sourceContextDeclared
    h.targetContextDeclared h.translationPerformed h.semanticLossMaterial
    h.actorLinkBroken h.verificationAbsent h.boundaryGuardAbsent

def TranslationFailureProfileBlocked {M : SigmaModel}
    (profile : TranslationFailureProfile M) : Prop :=
  Or (Not profile.sourceContextDeclared)
    (Or (Not profile.targetContextDeclared)
      (Or (Not profile.translationPerformed)
        (Or (Not profile.semanticLossMaterial)
          (Or (Not profile.actorLinkBroken)
            (Or (Not profile.verificationAbsent)
              (Not profile.boundaryGuardAbsent))))))

theorem missing_source_context_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.sourceContextDeclared) :
    TranslationFailureProfileBlocked profile :=
  Or.inl h

theorem missing_target_context_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.targetContextDeclared) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem absent_translation_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.translationPerformed) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem immaterial_semantic_loss_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.semanticLossMaterial) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem intact_actor_link_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.actorLinkBroken) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem present_translation_verification_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.verificationAbsent) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_translation_boundary_blocks_translation {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    TranslationFailureProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def TranslationFailureProfile.toMechanismProfile {M : SigmaModel}
    (profile : TranslationFailureProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M6
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.sourceContextDeclared
    triggerPresent := profile.targetContextDeclared
    claimBasisAvailable := profile.translationPerformed
    supportBasisAvailable := profile.semanticLossMaterial
    adequacyStandardDeclared := profile.actorLinkBroken
    evaluatorBoundaryDeclared := profile.verificationAbsent
    nonCollapseBoundaryDeclared := profile.boundaryGuardAbsent }

theorem TranslationFailureProfile_mechanism_label {M : SigmaModel}
    (profile : TranslationFailureProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M6 := rfl

theorem TranslationFailureProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : TranslationFailureProfile M)
    (h : TranslationFailureProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.sourceContextDeclared
    trigger := h.targetContextDeclared
    claimBasis := h.translationPerformed
    supportBasis := h.semanticLossMaterial
    adequacy := h.actorLinkBroken
    evaluatorBoundary := h.verificationAbsent
    nonCollapseBoundary := h.boundaryGuardAbsent }

structure M6TranslationFailureCase (M : SigmaModel) where
  profile : TranslationFailureProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M6TranslationFailureSatisfied {M : SigmaModel}
    (caseData : M6TranslationFailureCase M) : Prop where
  translationProfileSatisfied :
    TranslationFailureProfileSatisfied caseData.profile

theorem M6TranslationFailureCase_to_ISFSem {M : SigmaModel}
    (caseData : M6TranslationFailureCase M)
    (h : M6TranslationFailureSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      TranslationFailureProfile_to_supportDegraded caseData.profile
        h.translationProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def translationFailureOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def translationFailureOnlyModel : SigmaModel :=
  UnitPredicateModel translationFailureOnlyTruth

def translationFailureOnlyProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := TranslationFailureMode.semanticLoss
    sourceContextDeclared := True
    targetContextDeclared := True
    translationPerformed := True
    semanticLossMaterial := True
    actorLinkBroken := True
    verificationAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem translationFailureOnlyProfile_satisfied :
    TranslationFailureProfileSatisfied translationFailureOnlyProfile :=
  { sourceContextDeclared := True.intro
    targetContextDeclared := True.intro
    translationPerformed := True.intro
    semanticLossMaterial := True.intro
    actorLinkBroken := True.intro
    verificationAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def translationFailureNoSourceProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    sourceContextDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def translationFailureNoTargetProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    targetContextDeclared := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def translationFailureAbsentProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    translationPerformed := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def translationFailureImmaterialLossProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    semanticLossMaterial := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def translationFailureLinkIntactProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    actorLinkBroken := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def translationFailureVerifiedProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    verificationAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def translationFailureBoundaryPresentProfile :
    TranslationFailureProfile translationFailureOnlyModel :=
  { translationFailureOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem translationFailureNoSourceProfile_blocked :
    TranslationFailureProfileBlocked translationFailureNoSourceProfile :=
  missing_source_context_blocks_translation translationFailureNoSourceProfile
    (by
      intro h
      cases h)

theorem translationFailureNoTargetProfile_blocked :
    TranslationFailureProfileBlocked translationFailureNoTargetProfile :=
  missing_target_context_blocks_translation translationFailureNoTargetProfile
    (by
      intro h
      cases h)

theorem translationFailureAbsentProfile_blocked :
    TranslationFailureProfileBlocked translationFailureAbsentProfile :=
  absent_translation_blocks_translation translationFailureAbsentProfile
    (by
      intro h
      cases h)

theorem translationFailureImmaterialLossProfile_blocked :
    TranslationFailureProfileBlocked
      translationFailureImmaterialLossProfile :=
  immaterial_semantic_loss_blocks_translation
    translationFailureImmaterialLossProfile
    (by
      intro h
      cases h)

theorem translationFailureLinkIntactProfile_blocked :
    TranslationFailureProfileBlocked translationFailureLinkIntactProfile :=
  intact_actor_link_blocks_translation translationFailureLinkIntactProfile
    (by
      intro h
      cases h)

theorem translationFailureVerifiedProfile_blocked :
    TranslationFailureProfileBlocked translationFailureVerifiedProfile :=
  present_translation_verification_blocks_translation
    translationFailureVerifiedProfile
    (by
      intro h
      cases h)

theorem translationFailureBoundaryPresentProfile_blocked :
    TranslationFailureProfileBlocked
      translationFailureBoundaryPresentProfile :=
  present_translation_boundary_blocks_translation
    translationFailureBoundaryPresentProfile
    (by
      intro h
      cases h)

def translationFailureOnlyCase :
    M6TranslationFailureCase translationFailureOnlyModel :=
  { profile := translationFailureOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem translationFailureOnlyCase_satisfied :
    M6TranslationFailureSatisfied translationFailureOnlyCase :=
  { translationProfileSatisfied := translationFailureOnlyProfile_satisfied }

theorem translationFailureOnly_supportDegraded :
    SupportDegradedSem (M := translationFailureOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  TranslationFailureProfile_to_supportDegraded translationFailureOnlyProfile
    translationFailureOnlyProfile_satisfied

theorem translationFailureOnly_to_ISFSem :
    ISFSem translationFailureOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit :=
  M6TranslationFailureCase_to_ISFSem translationFailureOnlyCase
    translationFailureOnlyCase_satisfied

theorem translationFailureOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      translationFailureOnlyProfile.toMechanismProfile :=
  TranslationFailureProfile_to_mechanism_satisfied
    translationFailureOnlyProfile
    translationFailureOnlyProfile_satisfied

end Paralogic
