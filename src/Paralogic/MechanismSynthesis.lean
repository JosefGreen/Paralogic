import Paralogic.ISFTMechanisms

/-!
Candidate synthesis layer for ISFT mechanism semantics.

This module is deliberately not a claim that M1-M12 are complete or externally
validated.  It creates a checked tier for candidate definitions: each mechanism
can be paired with an academic lens, an operational trigger, a failure
contrast, a boundary guard, and an empirical plan before it is promoted to
source-backed or empirically validated status.
-/

namespace Paralogic

inductive MechanismSemanticMaturity where
  | labelOnly
  | candidateSynthesized
  | sourceBacked
  | empiricallyValidated
  deriving DecidableEq, Repr

inductive MechanismLens where
  | evidentialAdequacy
  | metricProxy
  | accessSubstitution
  | symbolicPower
  | repairRevision
  | translationNetwork
  | conceptEssentialization
  | powerErasure
  | vetoSuppression
  | frameAnalysis
  | symbolicLoad
  | legitimacy
  deriving DecidableEq, Repr

def mechanismLens : ISFTMechanism -> MechanismLens
  | ISFTMechanism.M1 => MechanismLens.evidentialAdequacy
  | ISFTMechanism.M2 => MechanismLens.metricProxy
  | ISFTMechanism.M3 => MechanismLens.accessSubstitution
  | ISFTMechanism.M4 => MechanismLens.symbolicPower
  | ISFTMechanism.M5 => MechanismLens.repairRevision
  | ISFTMechanism.M6 => MechanismLens.translationNetwork
  | ISFTMechanism.M7 => MechanismLens.conceptEssentialization
  | ISFTMechanism.M8 => MechanismLens.powerErasure
  | ISFTMechanism.M9 => MechanismLens.vetoSuppression
  | ISFTMechanism.M10 => MechanismLens.frameAnalysis
  | ISFTMechanism.M11 => MechanismLens.symbolicLoad
  | ISFTMechanism.M12 => MechanismLens.legitimacy

inductive CandidateFailureAxis where
  | evidenceScopeMismatch
  | proxyGoalCollapse
  | formalAccessMismatch
  | symbolicRepresentationMismatch
  | repairClosureFailure
  | translationLoss
  | categoryIntentOverreach
  | powerConditionOmission
  | participationSuppression
  | contextFrameDrift
  | symbolInterpretationOverload
  | legitimacyOverextension
  deriving DecidableEq, Repr

def mechanismFailureAxis : ISFTMechanism -> CandidateFailureAxis
  | ISFTMechanism.M1 => CandidateFailureAxis.evidenceScopeMismatch
  | ISFTMechanism.M2 => CandidateFailureAxis.proxyGoalCollapse
  | ISFTMechanism.M3 => CandidateFailureAxis.formalAccessMismatch
  | ISFTMechanism.M4 => CandidateFailureAxis.symbolicRepresentationMismatch
  | ISFTMechanism.M5 => CandidateFailureAxis.repairClosureFailure
  | ISFTMechanism.M6 => CandidateFailureAxis.translationLoss
  | ISFTMechanism.M7 => CandidateFailureAxis.categoryIntentOverreach
  | ISFTMechanism.M8 => CandidateFailureAxis.powerConditionOmission
  | ISFTMechanism.M9 => CandidateFailureAxis.participationSuppression
  | ISFTMechanism.M10 => CandidateFailureAxis.contextFrameDrift
  | ISFTMechanism.M11 => CandidateFailureAxis.symbolInterpretationOverload
  | ISFTMechanism.M12 => CandidateFailureAxis.legitimacyOverextension

structure CandidateMechanismDefinition (M : SigmaModel) where
  mechanism : ISFTMechanism
  maturity : MechanismSemanticMaturity
  lens : MechanismLens
  failureAxis : CandidateFailureAxis
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  sourceTraceDeclared : Prop
  lensFitDeclared : Prop
  operationalTriggerDeclared : Prop
  failureContrastDeclared : Prop
  boundaryGuardDeclared : Prop
  empiricalCodingPlanDeclared : Prop
  nonCollapseGuardDeclared : Prop

def CandidateMechanismDefinitionWellLensed {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M) : Prop :=
  And (candidate.lens = mechanismLens candidate.mechanism)
    (candidate.failureAxis = mechanismFailureAxis candidate.mechanism)

def CandidateMechanismDefinitionSatisfied {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M) : Prop :=
  And (candidate.maturity = MechanismSemanticMaturity.candidateSynthesized)
    (And (CandidateMechanismDefinitionWellLensed candidate)
      (And candidate.sourceTraceDeclared
        (And candidate.lensFitDeclared
          (And candidate.operationalTriggerDeclared
            (And candidate.failureContrastDeclared
              (And candidate.boundaryGuardDeclared
                (And candidate.empiricalCodingPlanDeclared
                  candidate.nonCollapseGuardDeclared)))))))

def CandidateMechanismDefinitionBlocked {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M) : Prop :=
  Or (Not (candidate.maturity = MechanismSemanticMaturity.candidateSynthesized))
    (Or (Not (CandidateMechanismDefinitionWellLensed candidate))
      (Or (Not candidate.sourceTraceDeclared)
        (Or (Not candidate.lensFitDeclared)
          (Or (Not candidate.operationalTriggerDeclared)
            (Or (Not candidate.failureContrastDeclared)
              (Or (Not candidate.boundaryGuardDeclared)
                (Or (Not candidate.empiricalCodingPlanDeclared)
                  (Not candidate.nonCollapseGuardDeclared))))))))

def CandidateMechanismDefinition.toMechanismProfile {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M) : ISFTMechanismProfile M :=
  { mechanism := candidate.mechanism
    institution := candidate.institution
    output := candidate.output
    claim := candidate.claim
    evidence := candidate.evidence
    context := candidate.context
    domainDeclared := candidate.sourceTraceDeclared
    triggerPresent := candidate.operationalTriggerDeclared
    claimBasisAvailable := candidate.lensFitDeclared
    supportBasisAvailable := candidate.failureContrastDeclared
    adequacyStandardDeclared := candidate.boundaryGuardDeclared
    evaluatorBoundaryDeclared := candidate.empiricalCodingPlanDeclared
    nonCollapseBoundaryDeclared := candidate.nonCollapseGuardDeclared }

theorem candidate_satisfied_to_mechanism_profile_satisfied {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M)
    (h : CandidateMechanismDefinitionSatisfied candidate) :
    ISFTMechanismProfileSatisfied candidate.toMechanismProfile :=
  { domain := h.right.right.left
    trigger := h.right.right.right.right.left
    claimBasis := h.right.right.right.left
    supportBasis := h.right.right.right.right.right.left
    adequacy := h.right.right.right.right.right.right.left
    evaluatorBoundary := h.right.right.right.right.right.right.right.left
    nonCollapseBoundary := h.right.right.right.right.right.right.right.right }

theorem missing_candidate_source_trace_blocks {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M)
    (h : Not candidate.sourceTraceDeclared) :
    CandidateMechanismDefinitionBlocked candidate :=
  Or.inr (Or.inr (Or.inl h))

theorem wrong_candidate_lens_blocks {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M)
    (h : Not (CandidateMechanismDefinitionWellLensed candidate)) :
    CandidateMechanismDefinitionBlocked candidate :=
  Or.inr (Or.inl h)

theorem candidate_synthesized_not_source_backed {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M)
    (h : candidate.maturity = MechanismSemanticMaturity.candidateSynthesized) :
    Not (candidate.maturity = MechanismSemanticMaturity.sourceBacked) := by
  intro hSource
  rw [hSource] at h
  cases h

theorem candidate_synthesized_not_empirically_validated {M : SigmaModel}
    (candidate : CandidateMechanismDefinition M)
    (h : candidate.maturity = MechanismSemanticMaturity.candidateSynthesized) :
    Not (candidate.maturity = MechanismSemanticMaturity.empiricallyValidated) := by
  intro hEmpirical
  rw [hEmpirical] at h
  cases h

theorem M1_lens_is_evidential :
    mechanismLens ISFTMechanism.M1 = MechanismLens.evidentialAdequacy := rfl

theorem M2_lens_is_metric_proxy :
    mechanismLens ISFTMechanism.M2 = MechanismLens.metricProxy := rfl

theorem M7_lens_is_concept_essentialization :
    mechanismLens ISFTMechanism.M7 =
      MechanismLens.conceptEssentialization := rfl

theorem M8_lens_is_power_erasure :
    mechanismLens ISFTMechanism.M8 = MechanismLens.powerErasure := rfl

theorem M12_lens_is_legitimacy :
    mechanismLens ISFTMechanism.M12 = MechanismLens.legitimacy := rfl

def candidateUnitModel : SigmaModel :=
  UnitPredicateModel (fun _ => True)

def unitCandidateDefinition (mechanism : ISFTMechanism) :
    CandidateMechanismDefinition candidateUnitModel :=
  { mechanism := mechanism
    maturity := MechanismSemanticMaturity.candidateSynthesized
    lens := mechanismLens mechanism
    failureAxis := mechanismFailureAxis mechanism
    institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    sourceTraceDeclared := True
    lensFitDeclared := True
    operationalTriggerDeclared := True
    failureContrastDeclared := True
    boundaryGuardDeclared := True
    empiricalCodingPlanDeclared := True
    nonCollapseGuardDeclared := True }

theorem unit_candidate_definition_satisfied (mechanism : ISFTMechanism) :
    CandidateMechanismDefinitionSatisfied
      (unitCandidateDefinition mechanism) := by
  exact And.intro rfl
    (And.intro (And.intro rfl rfl)
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro
              (And.intro True.intro
                (And.intro True.intro True.intro)))))))

theorem unit_candidate_profile_satisfied (mechanism : ISFTMechanism) :
    ISFTMechanismProfileSatisfied
      (unitCandidateDefinition mechanism).toMechanismProfile :=
  candidate_satisfied_to_mechanism_profile_satisfied
    (unitCandidateDefinition mechanism)
    (unit_candidate_definition_satisfied mechanism)

def allISFTMechanisms : List ISFTMechanism :=
  [ISFTMechanism.M1, ISFTMechanism.M2, ISFTMechanism.M3,
    ISFTMechanism.M4, ISFTMechanism.M5, ISFTMechanism.M6,
    ISFTMechanism.M7, ISFTMechanism.M8, ISFTMechanism.M9,
    ISFTMechanism.M10, ISFTMechanism.M11, ISFTMechanism.M12]

theorem allISFTMechanisms_length :
    allISFTMechanisms.length = 12 := rfl

theorem allISFTMechanisms_covers (mechanism : ISFTMechanism) :
    mechanism ∈ allISFTMechanisms := by
  cases mechanism <;> simp [allISFTMechanisms]

theorem allISFTMechanisms_no_duplicates :
    allISFTMechanisms.Nodup := by
  decide

theorem mechanismIndex_positive (mechanism : ISFTMechanism) :
    0 < mechanismIndex mechanism := by
  cases mechanism <;> decide

theorem mechanismIndex_le_twelve (mechanism : ISFTMechanism) :
    mechanismIndex mechanism <= 12 := by
  cases mechanism <;> decide

structure CandidateMechanismMappingCertified
    (mechanism : ISFTMechanism) : Prop where
  listed : mechanism ∈ allISFTMechanisms
  indexPositive : 0 < mechanismIndex mechanism
  indexBounded : mechanismIndex mechanism <= 12
  lensAssigned :
    (unitCandidateDefinition mechanism).lens = mechanismLens mechanism
  failureAxisAssigned :
    (unitCandidateDefinition mechanism).failureAxis =
      mechanismFailureAxis mechanism
  labelPreserved :
    ((unitCandidateDefinition mechanism).toMechanismProfile).mechanism =
      mechanism

theorem unit_candidate_mapping_certified (mechanism : ISFTMechanism) :
    CandidateMechanismMappingCertified mechanism :=
  { listed := allISFTMechanisms_covers mechanism
    indexPositive := mechanismIndex_positive mechanism
    indexBounded := mechanismIndex_le_twelve mechanism
    lensAssigned := rfl
    failureAxisAssigned := rfl
    labelPreserved := rfl }

theorem all_candidate_mechanisms_not_source_backed
    (mechanism : ISFTMechanism) :
    Not
      ((unitCandidateDefinition mechanism).maturity =
        MechanismSemanticMaturity.sourceBacked) :=
  candidate_synthesized_not_source_backed
    (unitCandidateDefinition mechanism)
    rfl

theorem all_candidate_mechanisms_not_empirically_validated
    (mechanism : ISFTMechanism) :
    Not
      ((unitCandidateDefinition mechanism).maturity =
        MechanismSemanticMaturity.empiricallyValidated) :=
  candidate_synthesized_not_empirically_validated
    (unitCandidateDefinition mechanism)
    rfl

structure CandidateMechanismSurfaceCertified
    (mechanism : ISFTMechanism) : Prop where
  definitionSatisfied :
    CandidateMechanismDefinitionSatisfied
      (unitCandidateDefinition mechanism)
  profileSatisfied :
    ISFTMechanismProfileSatisfied
      (unitCandidateDefinition mechanism).toMechanismProfile
  notSourceBacked :
    Not
      ((unitCandidateDefinition mechanism).maturity =
        MechanismSemanticMaturity.sourceBacked)
  notEmpiricallyValidated :
    Not
      ((unitCandidateDefinition mechanism).maturity =
        MechanismSemanticMaturity.empiricallyValidated)

theorem unit_candidate_surface_certified (mechanism : ISFTMechanism) :
    CandidateMechanismSurfaceCertified mechanism :=
  { definitionSatisfied := unit_candidate_definition_satisfied mechanism
    profileSatisfied := unit_candidate_profile_satisfied mechanism
    notSourceBacked :=
      all_candidate_mechanisms_not_source_backed mechanism
    notEmpiricallyValidated :=
      all_candidate_mechanisms_not_empirically_validated mechanism }

def CandidateMechanismCoverageComplete : Prop :=
  forall mechanism : ISFTMechanism,
    And (CandidateMechanismMappingCertified mechanism)
      (CandidateMechanismSurfaceCertified mechanism)

theorem candidate_mechanism_coverage_complete :
    CandidateMechanismCoverageComplete := by
  intro mechanism
  exact And.intro
    (unit_candidate_mapping_certified mechanism)
    (unit_candidate_surface_certified mechanism)

end Paralogic
