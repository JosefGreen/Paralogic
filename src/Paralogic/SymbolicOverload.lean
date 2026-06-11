import Paralogic.ISFTMechanisms

/-!
M11 symbolic-overload semantics.

M11 is formalized as a local interpretation failure.  The profile records cases
where one symbolic output carries multiple material interpretations, those
interpretations conflict, and disambiguation controls are missing.
-/

namespace Paralogic

inductive SymbolicOverloadMode where
  | polysemy
  | roleConflation
  | audienceFragmentation
  | recursiveSignaling
  | institutionalLayering
  deriving DecidableEq, Repr

structure SymbolicOverloadProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : SymbolicOverloadMode
  symbolDeclared : Prop
  multipleInterpretationsPresent : Prop
  interpretationsConflict : Prop
  audienceUptakeMaterial : Prop
  claimDependsOnOverloadedSymbol : Prop
  disambiguationAbsent : Prop
  evaluatorResolutionAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    symbolDeclared ->
    multipleInterpretationsPresent ->
    interpretationsConflict ->
    audienceUptakeMaterial ->
    claimDependsOnOverloadedSymbol ->
    disambiguationAbsent ->
    evaluatorResolutionAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure SymbolicOverloadProfileSatisfied {M : SigmaModel}
    (profile : SymbolicOverloadProfile M) : Prop where
  symbolDeclared : profile.symbolDeclared
  multipleInterpretationsPresent : profile.multipleInterpretationsPresent
  interpretationsConflict : profile.interpretationsConflict
  audienceUptakeMaterial : profile.audienceUptakeMaterial
  claimDependsOnOverloadedSymbol : profile.claimDependsOnOverloadedSymbol
  disambiguationAbsent : profile.disambiguationAbsent
  evaluatorResolutionAbsent : profile.evaluatorResolutionAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem SymbolicOverloadProfile_to_supportDegraded {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : SymbolicOverloadProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.symbolDeclared
    h.multipleInterpretationsPresent h.interpretationsConflict
    h.audienceUptakeMaterial h.claimDependsOnOverloadedSymbol
    h.disambiguationAbsent h.evaluatorResolutionAbsent
    h.boundaryGuardAbsent

def SymbolicOverloadProfileBlocked {M : SigmaModel}
    (profile : SymbolicOverloadProfile M) : Prop :=
  Or (Not profile.symbolDeclared)
    (Or (Not profile.multipleInterpretationsPresent)
      (Or (Not profile.interpretationsConflict)
        (Or (Not profile.audienceUptakeMaterial)
          (Or (Not profile.claimDependsOnOverloadedSymbol)
            (Or (Not profile.disambiguationAbsent)
              (Or (Not profile.evaluatorResolutionAbsent)
                (Not profile.boundaryGuardAbsent)))))))

theorem missing_overload_symbol_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.symbolDeclared) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inl h

theorem single_interpretation_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.multipleInterpretationsPresent) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem compatible_interpretations_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.interpretationsConflict) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem immaterial_overload_uptake_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.audienceUptakeMaterial) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem independent_claim_blocks_overload_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.claimDependsOnOverloadedSymbol) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem present_disambiguation_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.disambiguationAbsent) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_evaluator_resolution_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.evaluatorResolutionAbsent) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem present_overload_boundary_blocks_profile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    SymbolicOverloadProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

def SymbolicOverloadProfile.toMechanismProfile {M : SigmaModel}
    (profile : SymbolicOverloadProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M11
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.symbolDeclared
    triggerPresent := profile.multipleInterpretationsPresent
    claimBasisAvailable := profile.interpretationsConflict
    supportBasisAvailable := profile.audienceUptakeMaterial
    adequacyStandardDeclared := profile.claimDependsOnOverloadedSymbol
    evaluatorBoundaryDeclared :=
      And profile.disambiguationAbsent profile.evaluatorResolutionAbsent
    nonCollapseBoundaryDeclared := profile.boundaryGuardAbsent }

theorem SymbolicOverloadProfile_mechanism_label {M : SigmaModel}
    (profile : SymbolicOverloadProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M11 := rfl

theorem SymbolicOverloadProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : SymbolicOverloadProfile M)
    (h : SymbolicOverloadProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.symbolDeclared
    trigger := h.multipleInterpretationsPresent
    claimBasis := h.interpretationsConflict
    supportBasis := h.audienceUptakeMaterial
    adequacy := h.claimDependsOnOverloadedSymbol
    evaluatorBoundary :=
      And.intro h.disambiguationAbsent h.evaluatorResolutionAbsent
    nonCollapseBoundary := h.boundaryGuardAbsent }

structure M11SymbolicOverloadCase (M : SigmaModel) where
  profile : SymbolicOverloadProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M11SymbolicOverloadSatisfied {M : SigmaModel}
    (caseData : M11SymbolicOverloadCase M) : Prop where
  overloadProfileSatisfied :
    SymbolicOverloadProfileSatisfied caseData.profile

theorem M11SymbolicOverloadCase_to_ISFSem {M : SigmaModel}
    (caseData : M11SymbolicOverloadCase M)
    (h : M11SymbolicOverloadSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      SymbolicOverloadProfile_to_supportDegraded caseData.profile
        h.overloadProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def symbolicOverloadOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def symbolicOverloadOnlyModel : SigmaModel :=
  UnitPredicateModel symbolicOverloadOnlyTruth

def symbolicOverloadOnlyProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := SymbolicOverloadMode.polysemy
    symbolDeclared := True
    multipleInterpretationsPresent := True
    interpretationsConflict := True
    audienceUptakeMaterial := True
    claimDependsOnOverloadedSymbol := True
    disambiguationAbsent := True
    evaluatorResolutionAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ _ => True.intro }

theorem symbolicOverloadOnlyProfile_satisfied :
    SymbolicOverloadProfileSatisfied symbolicOverloadOnlyProfile :=
  { symbolDeclared := True.intro
    multipleInterpretationsPresent := True.intro
    interpretationsConflict := True.intro
    audienceUptakeMaterial := True.intro
    claimDependsOnOverloadedSymbol := True.intro
    disambiguationAbsent := True.intro
    evaluatorResolutionAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def symbolicOverloadNoSymbolProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    symbolDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ _ => False.elim h }

def symbolicOverloadSingleMeaningProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    multipleInterpretationsPresent := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ _ => False.elim h }

def symbolicOverloadCompatibleProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    interpretationsConflict := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ _ => False.elim h }

def symbolicOverloadImmaterialUptakeProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    audienceUptakeMaterial := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ _ => False.elim h }

def symbolicOverloadIndependentClaimProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    claimDependsOnOverloadedSymbol := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ _ => False.elim h }

def symbolicOverloadDisambiguatedProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    disambiguationAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ _ => False.elim h }

def symbolicOverloadEvaluatorResolvedProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    evaluatorResolutionAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h _ => False.elim h }

def symbolicOverloadBoundaryPresentProfile :
    SymbolicOverloadProfile symbolicOverloadOnlyModel :=
  { symbolicOverloadOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ _ h => False.elim h }

theorem symbolicOverloadNoSymbolProfile_blocked :
    SymbolicOverloadProfileBlocked symbolicOverloadNoSymbolProfile :=
  missing_overload_symbol_blocks_profile symbolicOverloadNoSymbolProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadSingleMeaningProfile_blocked :
    SymbolicOverloadProfileBlocked symbolicOverloadSingleMeaningProfile :=
  single_interpretation_blocks_profile
    symbolicOverloadSingleMeaningProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadCompatibleProfile_blocked :
    SymbolicOverloadProfileBlocked symbolicOverloadCompatibleProfile :=
  compatible_interpretations_blocks_profile
    symbolicOverloadCompatibleProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadImmaterialUptakeProfile_blocked :
    SymbolicOverloadProfileBlocked
      symbolicOverloadImmaterialUptakeProfile :=
  immaterial_overload_uptake_blocks_profile
    symbolicOverloadImmaterialUptakeProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadIndependentClaimProfile_blocked :
    SymbolicOverloadProfileBlocked
      symbolicOverloadIndependentClaimProfile :=
  independent_claim_blocks_overload_profile
    symbolicOverloadIndependentClaimProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadDisambiguatedProfile_blocked :
    SymbolicOverloadProfileBlocked
      symbolicOverloadDisambiguatedProfile :=
  present_disambiguation_blocks_profile
    symbolicOverloadDisambiguatedProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadEvaluatorResolvedProfile_blocked :
    SymbolicOverloadProfileBlocked
      symbolicOverloadEvaluatorResolvedProfile :=
  present_evaluator_resolution_blocks_profile
    symbolicOverloadEvaluatorResolvedProfile
    (by
      intro h
      cases h)

theorem symbolicOverloadBoundaryPresentProfile_blocked :
    SymbolicOverloadProfileBlocked
      symbolicOverloadBoundaryPresentProfile :=
  present_overload_boundary_blocks_profile
    symbolicOverloadBoundaryPresentProfile
    (by
      intro h
      cases h)

def symbolicOverloadOnlyCase :
    M11SymbolicOverloadCase symbolicOverloadOnlyModel :=
  { profile := symbolicOverloadOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem symbolicOverloadOnlyCase_satisfied :
    M11SymbolicOverloadSatisfied symbolicOverloadOnlyCase :=
  { overloadProfileSatisfied := symbolicOverloadOnlyProfile_satisfied }

theorem symbolicOverloadOnly_supportDegraded :
    SupportDegradedSem (M := symbolicOverloadOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  SymbolicOverloadProfile_to_supportDegraded
    symbolicOverloadOnlyProfile
    symbolicOverloadOnlyProfile_satisfied

theorem symbolicOverloadOnly_to_ISFSem :
    ISFSem symbolicOverloadOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  M11SymbolicOverloadCase_to_ISFSem symbolicOverloadOnlyCase
    symbolicOverloadOnlyCase_satisfied

theorem symbolicOverloadOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      symbolicOverloadOnlyProfile.toMechanismProfile :=
  SymbolicOverloadProfile_to_mechanism_satisfied
    symbolicOverloadOnlyProfile
    symbolicOverloadOnlyProfile_satisfied

end Paralogic
