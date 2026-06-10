import Paralogic.ModelSemantics
import Paralogic.M8Power

/-!
Typed ISFT mechanism scaffold.

This module gives M1-M12 a checked mathematical surface without inventing
domain meanings not yet present in the repository.  Each mechanism is a label
with explicit activation conditions, dependency-graph structure, bounded-suite
coverage, and non-collapse witnesses.  M8 is connected to the developed
power-erasure profile; M12 is represented as a boundary profile until a richer
source-backed semantics is supplied.
-/

namespace Paralogic

inductive ISFTMechanism where
  | M1
  | M2
  | M3
  | M4
  | M5
  | M6
  | M7
  | M8
  | M9
  | M10
  | M11
  | M12
  deriving DecidableEq, Repr

def mechanismIndex : ISFTMechanism -> Nat
  | ISFTMechanism.M1 => 1
  | ISFTMechanism.M2 => 2
  | ISFTMechanism.M3 => 3
  | ISFTMechanism.M4 => 4
  | ISFTMechanism.M5 => 5
  | ISFTMechanism.M6 => 6
  | ISFTMechanism.M7 => 7
  | ISFTMechanism.M8 => 8
  | ISFTMechanism.M9 => 9
  | ISFTMechanism.M10 => 10
  | ISFTMechanism.M11 => 11
  | ISFTMechanism.M12 => 12

def mechanismName : ISFTMechanism -> String
  | ISFTMechanism.M1 => "Evidence Overclaim"
  | ISFTMechanism.M2 => "Metric-as-Value Collapse"
  | ISFTMechanism.M3 => "Formal Access Substitution"
  | ISFTMechanism.M4 => "Symbolic Substitution"
  | ISFTMechanism.M5 => "Repair Failure"
  | ISFTMechanism.M6 => "Translation Failure"
  | ISFTMechanism.M7 => "Category Essentialization"
  | ISFTMechanism.M8 => "Power Erasure"
  | ISFTMechanism.M9 => "Veto Suppression"
  | ISFTMechanism.M10 => "Frame Drift"
  | ISFTMechanism.M11 => "Symbolic Overload"
  | ISFTMechanism.M12 => "Legitimacy Claim Decay"

inductive WorkbookMechanismStatus where
  | accepted
  | pending
  deriving DecidableEq, Repr

def workbookMechanismStatus : ISFTMechanism -> WorkbookMechanismStatus
  | ISFTMechanism.M8 => WorkbookMechanismStatus.pending
  | ISFTMechanism.M12 => WorkbookMechanismStatus.pending
  | _ => WorkbookMechanismStatus.accepted

def WorkbookAcceptedMechanism (m : ISFTMechanism) : Prop :=
  workbookMechanismStatus m = WorkbookMechanismStatus.accepted

def WorkbookPendingMechanism (m : ISFTMechanism) : Prop :=
  workbookMechanismStatus m = WorkbookMechanismStatus.pending

theorem mechanismIndex_M8 : mechanismIndex ISFTMechanism.M8 = 8 := rfl

theorem mechanismIndex_M12 : mechanismIndex ISFTMechanism.M12 = 12 := rfl

theorem M8_ne_M12 : Not (ISFTMechanism.M8 = ISFTMechanism.M12) := by
  intro h
  cases h

theorem workbook_M1_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M1 := rfl

theorem workbook_M2_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M2 := rfl

theorem workbook_M3_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M3 := rfl

theorem workbook_M4_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M4 := rfl

theorem workbook_M5_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M5 := rfl

theorem workbook_M6_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M6 := rfl

theorem workbook_M7_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M7 := rfl

theorem workbook_M9_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M9 := rfl

theorem workbook_M10_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M10 := rfl

theorem workbook_M11_accepted :
    WorkbookAcceptedMechanism ISFTMechanism.M11 := rfl

theorem workbook_M8_pending :
    WorkbookPendingMechanism ISFTMechanism.M8 := rfl

theorem workbook_M12_pending :
    WorkbookPendingMechanism ISFTMechanism.M12 := rfl

theorem workbook_M8_not_accepted :
    Not (WorkbookAcceptedMechanism ISFTMechanism.M8) := by
  intro h
  cases h

theorem workbook_M12_not_accepted :
    Not (WorkbookAcceptedMechanism ISFTMechanism.M12) := by
  intro h
  cases h

structure ISFTMechanismProfile (M : SigmaModel) where
  mechanism : ISFTMechanism
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  domainDeclared : Prop
  triggerPresent : Prop
  claimBasisAvailable : Prop
  supportBasisAvailable : Prop
  adequacyStandardDeclared : Prop
  evaluatorBoundaryDeclared : Prop
  nonCollapseBoundaryDeclared : Prop

structure ISFTMechanismProfileSatisfied {M : SigmaModel}
    (profile : ISFTMechanismProfile M) : Prop where
  domain : profile.domainDeclared
  trigger : profile.triggerPresent
  claimBasis : profile.claimBasisAvailable
  supportBasis : profile.supportBasisAvailable
  adequacy : profile.adequacyStandardDeclared
  evaluatorBoundary : profile.evaluatorBoundaryDeclared
  nonCollapseBoundary : profile.nonCollapseBoundaryDeclared

def ISFTMechanismProfileBlocked {M : SigmaModel}
    (profile : ISFTMechanismProfile M) : Prop :=
  Or (Not profile.domainDeclared)
    (Or (Not profile.triggerPresent)
      (Or (Not profile.claimBasisAvailable)
        (Or (Not profile.supportBasisAvailable)
          (Or (Not profile.adequacyStandardDeclared)
            (Or (Not profile.evaluatorBoundaryDeclared)
              (Not profile.nonCollapseBoundaryDeclared))))))

theorem missing_mechanism_domain_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.domainDeclared) :
    ISFTMechanismProfileBlocked profile :=
  Or.inl h

theorem missing_mechanism_trigger_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.triggerPresent) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem missing_mechanism_claim_basis_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.claimBasisAvailable) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem missing_mechanism_support_basis_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.supportBasisAvailable) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem missing_mechanism_adequacy_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.adequacyStandardDeclared) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem missing_mechanism_evaluator_boundary_blocks_profile {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.evaluatorBoundaryDeclared) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem missing_mechanism_noncollapse_boundary_blocks_profile
    {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : Not profile.nonCollapseBoundaryDeclared) :
    ISFTMechanismProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

structure ISFTMechanismCase (M : SigmaModel) where
  profile : ISFTMechanismProfile M
  satisfied : ISFTMechanismProfileSatisfied profile

def ISFTMechanismProfile.toCase {M : SigmaModel}
    (profile : ISFTMechanismProfile M)
    (h : ISFTMechanismProfileSatisfied profile) :
    ISFTMechanismCase M :=
  { profile := profile
    satisfied := h }

structure MechanismDependencyGraph where
  edge : ISFTMechanism -> ISFTMechanism -> Prop

def IndexIncreasingDependencyGraph (graph : MechanismDependencyGraph) : Prop :=
  forall source target : ISFTMechanism,
    graph.edge source target -> mechanismIndex source < mechanismIndex target

theorem index_increasing_graph_has_no_self_dependency
    (graph : MechanismDependencyGraph)
    (hinc : IndexIncreasingDependencyGraph graph)
    (m : ISFTMechanism) :
    Not (graph.edge m m) := by
  intro hedge
  exact (Nat.lt_irrefl (mechanismIndex m)) (hinc m m hedge)

def linearMechanismGraph : MechanismDependencyGraph :=
  { edge := fun source target => mechanismIndex source + 1 = mechanismIndex target }

theorem linear_graph_M1_to_M2 :
    linearMechanismGraph.edge ISFTMechanism.M1 ISFTMechanism.M2 := rfl

theorem linear_graph_M7_to_M8 :
    linearMechanismGraph.edge ISFTMechanism.M7 ISFTMechanism.M8 := rfl

theorem linear_graph_M11_to_M12 :
    linearMechanismGraph.edge ISFTMechanism.M11 ISFTMechanism.M12 := rfl

structure BoundedISFTSuite (M : SigmaModel) where
  profile : ISFTMechanism -> ISFTMechanismProfile M
  labelCorrect : forall m : ISFTMechanism, (profile m).mechanism = m
  satisfied : forall m : ISFTMechanism,
    ISFTMechanismProfileSatisfied (profile m)

def BoundedISFTSuiteComplete {M : SigmaModel}
    (suite : BoundedISFTSuite M) : Prop :=
  forall m : ISFTMechanism, ISFTMechanismProfileSatisfied (suite.profile m)

theorem bounded_suite_complete {M : SigmaModel}
    (suite : BoundedISFTSuite M) :
    BoundedISFTSuiteComplete suite :=
  suite.satisfied

theorem bounded_suite_covers_M8 {M : SigmaModel}
    (suite : BoundedISFTSuite M) :
    ISFTMechanismProfileSatisfied (suite.profile ISFTMechanism.M8) :=
  suite.satisfied ISFTMechanism.M8

theorem bounded_suite_covers_M12 {M : SigmaModel}
    (suite : BoundedISFTSuite M) :
    ISFTMechanismProfileSatisfied (suite.profile ISFTMechanism.M12) :=
  suite.satisfied ISFTMechanism.M12

def M8PowerErasureCase.toMechanismProfile {M : SigmaModel}
    (caseData : M8PowerErasureCase M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M8
    institution := caseData.powerProfile.institution
    output := caseData.powerProfile.output
    claim := caseData.claim
    evidence := caseData.evidence
    context := caseData.context
    domainDeclared := True
    triggerPresent := True
    claimBasisAvailable := True
    supportBasisAvailable := True
    adequacyStandardDeclared := True
    evaluatorBoundaryDeclared := True
    nonCollapseBoundaryDeclared := True }

theorem M8PowerErasureCase_mechanism_label {M : SigmaModel}
    (caseData : M8PowerErasureCase M) :
    (caseData.toMechanismProfile).mechanism = ISFTMechanism.M8 := rfl

theorem M8PowerErasureCase_mechanism_profile_satisfied {M : SigmaModel}
    (caseData : M8PowerErasureCase M) :
    ISFTMechanismProfileSatisfied caseData.toMechanismProfile :=
  { domain := True.intro
    trigger := True.intro
    claimBasis := True.intro
    supportBasis := True.intro
    adequacy := True.intro
    evaluatorBoundary := True.intro
    nonCollapseBoundary := True.intro }

theorem M8_mechanism_power_case_to_M8Sem {M : SigmaModel}
    (caseData : M8PowerErasureCase M)
    (h : M8PowerErasureSatisfied caseData) :
    M8Sem M caseData.powerProfile.institution caseData.powerProfile.output
      caseData.claim caseData.evidence caseData.context
      caseData.powerProfile.condition caseData.powerProfile.group :=
  M8PowerErasureCase_to_M8Sem caseData h

structure M12BoundaryProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  mechanismBoundaryDeclared : Prop
  upstreamMechanismsEnumerated : Prop
  outputScopeBounded : Prop
  nonFinalityDeclared : Prop
  bridgeSeparationDeclared : Prop
  empiricalSeparationDeclared : Prop

structure M12BoundaryProfileSatisfied {M : SigmaModel}
    (profile : M12BoundaryProfile M) : Prop where
  boundary : profile.mechanismBoundaryDeclared
  upstream : profile.upstreamMechanismsEnumerated
  boundedScope : profile.outputScopeBounded
  nonFinality : profile.nonFinalityDeclared
  bridgeSeparation : profile.bridgeSeparationDeclared
  empiricalSeparation : profile.empiricalSeparationDeclared

def M12BoundaryProfileBlocked {M : SigmaModel}
    (profile : M12BoundaryProfile M) : Prop :=
  Or (Not profile.mechanismBoundaryDeclared)
    (Or (Not profile.upstreamMechanismsEnumerated)
      (Or (Not profile.outputScopeBounded)
        (Or (Not profile.nonFinalityDeclared)
          (Or (Not profile.bridgeSeparationDeclared)
            (Not profile.empiricalSeparationDeclared)))))

theorem missing_M12_boundary_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.mechanismBoundaryDeclared) :
    M12BoundaryProfileBlocked profile :=
  Or.inl h

theorem missing_M12_upstream_enumeration_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.upstreamMechanismsEnumerated) :
    M12BoundaryProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem missing_M12_scope_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.outputScopeBounded) :
    M12BoundaryProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem missing_M12_nonfinality_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.nonFinalityDeclared) :
    M12BoundaryProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem missing_M12_bridge_separation_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.bridgeSeparationDeclared) :
    M12BoundaryProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem missing_M12_empirical_separation_blocks_profile {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : Not profile.empiricalSeparationDeclared) :
    M12BoundaryProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

def M12BoundaryProfile.toMechanismProfile {M : SigmaModel}
    (profile : M12BoundaryProfile M) : ISFTMechanismProfile M :=
  { mechanism := ISFTMechanism.M12
    institution := profile.institution
    output := profile.output
    claim := profile.claim
    evidence := profile.evidence
    context := profile.context
    domainDeclared := profile.mechanismBoundaryDeclared
    triggerPresent := profile.upstreamMechanismsEnumerated
    claimBasisAvailable := profile.outputScopeBounded
    supportBasisAvailable := profile.nonFinalityDeclared
    adequacyStandardDeclared := profile.bridgeSeparationDeclared
    evaluatorBoundaryDeclared := profile.mechanismBoundaryDeclared
    nonCollapseBoundaryDeclared := profile.empiricalSeparationDeclared }

theorem M12BoundaryProfile_mechanism_label {M : SigmaModel}
    (profile : M12BoundaryProfile M) :
    (profile.toMechanismProfile).mechanism = ISFTMechanism.M12 := rfl

theorem M12BoundaryProfile_to_mechanism_satisfied {M : SigmaModel}
    (profile : M12BoundaryProfile M)
    (h : M12BoundaryProfileSatisfied profile) :
    ISFTMechanismProfileSatisfied profile.toMechanismProfile :=
  { domain := h.boundary
    trigger := h.upstream
    claimBasis := h.boundedScope
    supportBasis := h.nonFinality
    adequacy := h.bridgeSeparation
    evaluatorBoundary := h.boundary
    nonCollapseBoundary := h.empiricalSeparation }

inductive SuppressionMode where
  | omission
  | masking
  | dilution
  | displacement
  | overload
  deriving DecidableEq, Repr

structure SuppressionProfile (M : SigmaModel) where
  mechanism : ISFTMechanism
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  claim : M.Carrier SortTag.claim
  mode : SuppressionMode
  supportBasisAvailable : Prop
  suppressionDetected : Prop
  suppressionMaterial : Prop
  scopeMatched : Prop
  warrantSupportDegraded :
    supportBasisAvailable ->
    suppressionDetected ->
    suppressionMaterial ->
    scopeMatched ->
    SupportDegradedSem evidence context claim

structure SuppressionProfileSatisfied {M : SigmaModel}
    (profile : SuppressionProfile M) : Prop where
  supportBasis : profile.supportBasisAvailable
  detected : profile.suppressionDetected
  material : profile.suppressionMaterial
  scopeMatched : profile.scopeMatched

theorem SuppressionProfile_to_supportDegraded {M : SigmaModel}
    (profile : SuppressionProfile M)
    (h : SuppressionProfileSatisfied profile) :
    SupportDegradedSem profile.evidence profile.context profile.claim :=
  profile.warrantSupportDegraded h.supportBasis h.detected h.material
    h.scopeMatched

def SuppressionProfileBlocked {M : SigmaModel}
    (profile : SuppressionProfile M) : Prop :=
  Or (Not profile.supportBasisAvailable)
    (Or (Not profile.suppressionDetected)
      (Or (Not profile.suppressionMaterial) (Not profile.scopeMatched)))

theorem missing_suppression_support_basis_blocks_profile {M : SigmaModel}
    (profile : SuppressionProfile M)
    (h : Not profile.supportBasisAvailable) :
    SuppressionProfileBlocked profile :=
  Or.inl h

theorem undetected_suppression_blocks_profile {M : SigmaModel}
    (profile : SuppressionProfile M)
    (h : Not profile.suppressionDetected) :
    SuppressionProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem immaterial_suppression_blocks_profile {M : SigmaModel}
    (profile : SuppressionProfile M)
    (h : Not profile.suppressionMaterial) :
    SuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem suppression_scope_mismatch_blocks_profile {M : SigmaModel}
    (profile : SuppressionProfile M)
    (h : Not profile.scopeMatched) :
    SuppressionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr h))

def mechanismOnlyTruth (_p : PredicateSymbol) : Prop := False

def mechanismOnlyModel : SigmaModel := UnitPredicateModel mechanismOnlyTruth

def suppressionOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.supportDegraded => True
  | _ => False

def suppressionOnlyModel : SigmaModel :=
  UnitPredicateModel suppressionOnlyTruth

def suppressionOnlyProfile :
    SuppressionProfile suppressionOnlyModel :=
  { mechanism := ISFTMechanism.M3
    evidence := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    mode := SuppressionMode.omission
    supportBasisAvailable := True
    suppressionDetected := True
    suppressionMaterial := True
    scopeMatched := True
    warrantSupportDegraded := fun _ _ _ _ => True.intro }

theorem suppressionOnlyProfile_satisfied :
    SuppressionProfileSatisfied suppressionOnlyProfile :=
  { supportBasis := True.intro
    detected := True.intro
    material := True.intro
    scopeMatched := True.intro }

theorem suppressionOnly_supportDegraded :
    SupportDegradedSem (M := suppressionOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  SuppressionProfile_to_supportDegraded suppressionOnlyProfile
    suppressionOnlyProfile_satisfied

theorem suppressionOnly_not_ISFSem :
    Not (ISFSem suppressionOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h.uses

def mechanismOnlyProfile (mechanism : ISFTMechanism) :
    ISFTMechanismProfile mechanismOnlyModel :=
  { mechanism := mechanism
    institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    domainDeclared := True
    triggerPresent := True
    claimBasisAvailable := True
    supportBasisAvailable := True
    adequacyStandardDeclared := True
    evaluatorBoundaryDeclared := True
    nonCollapseBoundaryDeclared := True }

theorem mechanismOnlyProfile_satisfied (mechanism : ISFTMechanism) :
    ISFTMechanismProfileSatisfied (mechanismOnlyProfile mechanism) :=
  { domain := True.intro
    trigger := True.intro
    claimBasis := True.intro
    supportBasis := True.intro
    adequacy := True.intro
    evaluatorBoundary := True.intro
    nonCollapseBoundary := True.intro }

def mechanismOnlySuite : BoundedISFTSuite mechanismOnlyModel :=
  { profile := mechanismOnlyProfile
    labelCorrect := fun _ => rfl
    satisfied := mechanismOnlyProfile_satisfied }

theorem mechanismOnlySuite_complete :
    BoundedISFTSuiteComplete mechanismOnlySuite :=
  bounded_suite_complete mechanismOnlySuite

theorem mechanismOnlySuite_covers_M8 :
    ISFTMechanismProfileSatisfied
      (mechanismOnlySuite.profile ISFTMechanism.M8) :=
  bounded_suite_covers_M8 mechanismOnlySuite

theorem mechanismOnlySuite_covers_M12 :
    ISFTMechanismProfileSatisfied
      (mechanismOnlySuite.profile ISFTMechanism.M12) :=
  bounded_suite_covers_M12 mechanismOnlySuite

def m12BoundaryOnlyProfile : M12BoundaryProfile mechanismOnlyModel :=
  { institution := Unit.unit
    output := Unit.unit
    claim := Unit.unit
    evidence := Unit.unit
    context := Unit.unit
    mechanismBoundaryDeclared := True
    upstreamMechanismsEnumerated := True
    outputScopeBounded := True
    nonFinalityDeclared := True
    bridgeSeparationDeclared := True
    empiricalSeparationDeclared := True }

theorem m12BoundaryOnlyProfile_satisfied :
    M12BoundaryProfileSatisfied m12BoundaryOnlyProfile :=
  { boundary := True.intro
    upstream := True.intro
    boundedScope := True.intro
    nonFinality := True.intro
    bridgeSeparation := True.intro
    empiricalSeparation := True.intro }

theorem m12BoundaryOnly_to_mechanism_satisfied :
    ISFTMechanismProfileSatisfied
      m12BoundaryOnlyProfile.toMechanismProfile :=
  M12BoundaryProfile_to_mechanism_satisfied m12BoundaryOnlyProfile
    m12BoundaryOnlyProfile_satisfied

theorem mechanismOnly_profile_not_ISFSem (_mechanism : ISFTMechanism) :
    Not (ISFSem mechanismOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h.uses

theorem mechanismOnly_M1_not_ISFSem :
    Not (ISFSem mechanismOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit) :=
  mechanismOnly_profile_not_ISFSem ISFTMechanism.M1

theorem mechanismOnly_M8_not_M8Sem :
    Not (M8Sem mechanismOnlyModel Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h.uses

theorem mechanismOnly_M12_not_ValidInsightSem :
    Not (ValidInsightSem mechanismOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem mechanismOnly_M12_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem mechanismOnlyModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

end Paralogic
