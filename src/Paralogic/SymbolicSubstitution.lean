import Paralogic.ISFTMechanisms

/-!
M4 symbolic-substitution semantics.

M4 is formalized as a local representation failure.  The profile records cases
where a symbol, label, or representation is treated as a substantive condition
even though representational fit, material grounding, correction, and boundary
conditions are missing.
-/

namespace Paralogic

inductive SymbolicSubstitutionMode where
  | labelReplacement
  | emblemReplacement
  | proxyNarrative
  | ceremonialRecognition
  | categoryToken
  deriving DecidableEq, Repr

structure SymbolicSubstitutionProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mode : SymbolicSubstitutionMode
  symbolDeclared : Prop
  symbolTreatedAsSubstantive : Prop
  representationMismatch : Prop
  materialConditionAbsent : Prop
  audienceUptakeMaterial : Prop
  correctionPathAbsent : Prop
  boundaryGuardAbsent : Prop
  warrantSupportDegraded :
    symbolDeclared ->
    symbolTreatedAsSubstantive ->
    representationMismatch ->
    materialConditionAbsent ->
    audienceUptakeMaterial ->
    correctionPathAbsent ->
    boundaryGuardAbsent ->
    SupportDegradedSem evidence context claim

structure SymbolicSubstitutionProfileSatisfied {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M) : Prop where
  symbolDeclared : profile.symbolDeclared
  symbolTreatedAsSubstantive : profile.symbolTreatedAsSubstantive
  representationMismatch : profile.representationMismatch
  materialConditionAbsent : profile.materialConditionAbsent
  audienceUptakeMaterial : profile.audienceUptakeMaterial
  correctionPathAbsent : profile.correctionPathAbsent
  boundaryGuardAbsent : profile.boundaryGuardAbsent

theorem SymbolicSubstitutionProfile_to_supportDegraded {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : SymbolicSubstitutionProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.symbolDeclared
    h.symbolTreatedAsSubstantive h.representationMismatch
    h.materialConditionAbsent h.audienceUptakeMaterial
    h.correctionPathAbsent h.boundaryGuardAbsent

def SymbolicSubstitutionProfileBlocked {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M) : Prop :=
  Or (Not profile.symbolDeclared)
    (Or (Not profile.symbolTreatedAsSubstantive)
      (Or (Not profile.representationMismatch)
        (Or (Not profile.materialConditionAbsent)
          (Or (Not profile.audienceUptakeMaterial)
            (Or (Not profile.correctionPathAbsent)
              (Not profile.boundaryGuardAbsent))))))

theorem missing_symbol_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.symbolDeclared) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inl h

theorem symbol_not_substituted_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.symbolTreatedAsSubstantive) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem matched_representation_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.representationMismatch) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem material_condition_present_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.materialConditionAbsent) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem immaterial_audience_uptake_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.audienceUptakeMaterial) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem present_symbolic_correction_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.correctionPathAbsent) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem present_symbolic_boundary_blocks_profile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : Not profile.boundaryGuardAbsent) :
    SymbolicSubstitutionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

def SymbolicSubstitutionProfile.toMechanismProfile {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M4
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.symbolDeclared
    triggerPresent := profile.symbolTreatedAsSubstantive
    claimBasisAvailable := profile.representationMismatch
    supportBasisAvailable := profile.materialConditionAbsent
    adequacyStandardDeclared := profile.audienceUptakeMaterial
    evaluatorBoundaryDeclared := profile.correctionPathAbsent
    nonCollapseBoundaryDeclared := profile.boundaryGuardAbsent }

theorem SymbolicSubstitutionProfile_mechanism_label {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M4 := rfl

theorem SymbolicSubstitutionProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : SymbolicSubstitutionProfile M)
    (h : SymbolicSubstitutionProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.symbolDeclared
    trigger := h.symbolTreatedAsSubstantive
    claimBasis := h.representationMismatch
    supportBasis := h.materialConditionAbsent
    adequacy := h.audienceUptakeMaterial
    evaluatorBoundary := h.correctionPathAbsent
    nonCollapseBoundary := h.boundaryGuardAbsent }

structure M4SymbolicSubstitutionCase (M : SigmaModel) where
  profile : SymbolicSubstitutionProfile M
  uses : UsesSem profile.institution profile.output
  claims : ClaimsSem profile.institution profile.output profile.claim
  treatsAsAdequate :
    TreatsAsAdequateSem profile.institution profile.output profile.claim
      profile.context

structure M4SymbolicSubstitutionSatisfied {M : SigmaModel}
    (caseData : M4SymbolicSubstitutionCase M) : Prop where
  symbolicProfileSatisfied :
    SymbolicSubstitutionProfileSatisfied caseData.profile

theorem M4SymbolicSubstitutionCase_to_ISFSem {M : SigmaModel}
    (caseData : M4SymbolicSubstitutionCase M)
    (h : M4SymbolicSubstitutionSatisfied caseData) :
    ISFSem M caseData.profile.institution caseData.profile.output
      caseData.profile.claim caseData.profile.evidence
      caseData.profile.context :=
  { uses := caseData.uses
    claims := caseData.claims
    supportDegraded :=
      SymbolicSubstitutionProfile_to_supportDegraded caseData.profile
        h.symbolicProfileSatisfied
    treatsAsAdequate := caseData.treatsAsAdequate }

def symbolicSubstitutionOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | _ => False

def symbolicSubstitutionOnlyModel : SigmaModel :=
  UnitPredicateModel symbolicSubstitutionOnlyTruth

def symbolicSubstitutionOnlyProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mode := SymbolicSubstitutionMode.labelReplacement
    symbolDeclared := True
    symbolTreatedAsSubstantive := True
    representationMismatch := True
    materialConditionAbsent := True
    audienceUptakeMaterial := True
    correctionPathAbsent := True
    boundaryGuardAbsent := True
    warrantSupportDegraded := fun _ _ _ _ _ _ _ => True.intro }

theorem symbolicSubstitutionOnlyProfile_satisfied :
    SymbolicSubstitutionProfileSatisfied symbolicSubstitutionOnlyProfile :=
  { symbolDeclared := True.intro
    symbolTreatedAsSubstantive := True.intro
    representationMismatch := True.intro
    materialConditionAbsent := True.intro
    audienceUptakeMaterial := True.intro
    correctionPathAbsent := True.intro
    boundaryGuardAbsent := True.intro }

def symbolicSubstitutionNoSymbolProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    symbolDeclared := False
    warrantSupportDegraded := fun h _ _ _ _ _ _ => False.elim h }

def symbolicSubstitutionNotSubstantiveProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    symbolTreatedAsSubstantive := False
    warrantSupportDegraded := fun _ h _ _ _ _ _ => False.elim h }

def symbolicSubstitutionMatchedProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    representationMismatch := False
    warrantSupportDegraded := fun _ _ h _ _ _ _ => False.elim h }

def symbolicSubstitutionMaterialPresentProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    materialConditionAbsent := False
    warrantSupportDegraded := fun _ _ _ h _ _ _ => False.elim h }

def symbolicSubstitutionImmaterialUptakeProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    audienceUptakeMaterial := False
    warrantSupportDegraded := fun _ _ _ _ h _ _ => False.elim h }

def symbolicSubstitutionCorrectionPresentProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    correctionPathAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ h _ => False.elim h }

def symbolicSubstitutionBoundaryPresentProfile :
    SymbolicSubstitutionProfile symbolicSubstitutionOnlyModel :=
  { symbolicSubstitutionOnlyProfile with
    boundaryGuardAbsent := False
    warrantSupportDegraded := fun _ _ _ _ _ _ h => False.elim h }

theorem symbolicSubstitutionNoSymbolProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionNoSymbolProfile :=
  missing_symbol_blocks_profile symbolicSubstitutionNoSymbolProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionNotSubstantiveProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionNotSubstantiveProfile :=
  symbol_not_substituted_blocks_profile
    symbolicSubstitutionNotSubstantiveProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionMatchedProfile_blocked :
    SymbolicSubstitutionProfileBlocked symbolicSubstitutionMatchedProfile :=
  matched_representation_blocks_profile symbolicSubstitutionMatchedProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionMaterialPresentProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionMaterialPresentProfile :=
  material_condition_present_blocks_profile
    symbolicSubstitutionMaterialPresentProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionImmaterialUptakeProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionImmaterialUptakeProfile :=
  immaterial_audience_uptake_blocks_profile
    symbolicSubstitutionImmaterialUptakeProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionCorrectionPresentProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionCorrectionPresentProfile :=
  present_symbolic_correction_blocks_profile
    symbolicSubstitutionCorrectionPresentProfile
    (by
      intro h
      cases h)

theorem symbolicSubstitutionBoundaryPresentProfile_blocked :
    SymbolicSubstitutionProfileBlocked
      symbolicSubstitutionBoundaryPresentProfile :=
  present_symbolic_boundary_blocks_profile
    symbolicSubstitutionBoundaryPresentProfile
    (by
      intro h
      cases h)

def symbolicSubstitutionOnlyCase :
    M4SymbolicSubstitutionCase symbolicSubstitutionOnlyModel :=
  { profile := symbolicSubstitutionOnlyProfile
    uses := True.intro
    claims := True.intro
    treatsAsAdequate := True.intro }

theorem symbolicSubstitutionOnlyCase_satisfied :
    M4SymbolicSubstitutionSatisfied symbolicSubstitutionOnlyCase :=
  { symbolicProfileSatisfied := symbolicSubstitutionOnlyProfile_satisfied }

theorem symbolicSubstitutionOnly_supportDegraded :
    SupportDegradedSem (M := symbolicSubstitutionOnlyModel) Unit.unit
      Unit.unit Unit.unit :=
  SymbolicSubstitutionProfile_to_supportDegraded
    symbolicSubstitutionOnlyProfile
    symbolicSubstitutionOnlyProfile_satisfied

theorem symbolicSubstitutionOnly_to_ISFSem :
    ISFSem symbolicSubstitutionOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  M4SymbolicSubstitutionCase_to_ISFSem symbolicSubstitutionOnlyCase
    symbolicSubstitutionOnlyCase_satisfied

theorem symbolicSubstitutionOnly_mechanism_profile_satisfied :
    ISFTMechanismProfileSatisfied
      symbolicSubstitutionOnlyProfile.toMechanismProfile :=
  SymbolicSubstitutionProfile_to_mechanism_satisfied
    symbolicSubstitutionOnlyProfile
    symbolicSubstitutionOnlyProfile_satisfied

end Paralogic
