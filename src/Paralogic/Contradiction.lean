import Paralogic.ModelSemantics

/-!
Contradiction calculus.

Contradiction is a typed semantic condition. It does not, by itself, imply
insight, truth, guilt, repair, empirical falsehood, or collapse.
-/

namespace Paralogic

structure ContradictionCase (M : SigmaModel) where
  kind : ContradictionKind
  frame : M.Carrier SortTag.frame
  context : M.Carrier SortTag.context
  claim : M.Carrier SortTag.claim
  present :
    M.interpPredicate PredicateSymbol.contradictionPresent
      (Args.cons frame (Args.cons context (Args.cons claim Args.nil)))

def ContradictionPresentSem {M : SigmaModel}
    (frame : M.Carrier SortTag.frame)
    (context : M.Carrier SortTag.context)
    (claim : M.Carrier SortTag.claim) : Prop :=
  M.interpPredicate PredicateSymbol.contradictionPresent
    (Args.cons frame (Args.cons context (Args.cons claim Args.nil)))

theorem ContradictionCase_to_present {M : SigmaModel}
    (c : ContradictionCase M) :
    ContradictionPresentSem c.frame c.context c.claim :=
  c.present

def LogicalContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.logical }

def SemanticContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.semantic }

def PragmaticContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.pragmatic }

def NormativeContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.normative }

def InstitutionalContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.institutional }

def FrameConflictCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.frameConflict }

def SupportTreatmentContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.supportTreatment }

def SymbolicContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.symbolic }

def SacredContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.sacred }

def ResidueContradictionCase (M : SigmaModel) : Type :=
  { c : ContradictionCase M // c.kind = ContradictionKind.residue }

theorem logical_case_to_present {M : SigmaModel}
    (c : LogicalContradictionCase M) :
    ContradictionPresentSem c.val.frame c.val.context c.val.claim :=
  c.val.present

theorem semantic_case_to_present {M : SigmaModel}
    (c : SemanticContradictionCase M) :
    ContradictionPresentSem c.val.frame c.val.context c.val.claim :=
  c.val.present

theorem support_treatment_case_to_present {M : SigmaModel}
    (c : SupportTreatmentContradictionCase M) :
    ContradictionPresentSem c.val.frame c.val.context c.val.claim :=
  c.val.present

structure ContradictionProfile (M : SigmaModel) where
  kind : ContradictionKind
  frame : M.Carrier SortTag.frame
  context : M.Carrier SortTag.context
  claim : M.Carrier SortTag.claim
  domainApplies : Prop
  incompatibilityDetected : Prop
  sameScope : Prop
  sameContext : Prop
  unresolved : Prop
  warrant :
    domainApplies ->
    incompatibilityDetected ->
    sameScope ->
    sameContext ->
    unresolved ->
    ContradictionPresentSem frame context claim

structure ContradictionProfileSatisfied {M : SigmaModel}
    (profile : ContradictionProfile M) : Prop where
  domainApplies : profile.domainApplies
  incompatibilityDetected : profile.incompatibilityDetected
  sameScope : profile.sameScope
  sameContext : profile.sameContext
  unresolved : profile.unresolved

def ContradictionProfile.toCase {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : ContradictionProfileSatisfied profile) :
    ContradictionCase M :=
  { kind := profile.kind
    frame := profile.frame
    context := profile.context
    claim := profile.claim
    present :=
      profile.warrant h.domainApplies h.incompatibilityDetected h.sameScope
        h.sameContext h.unresolved }

def ContradictionProfileBlocked {M : SigmaModel}
    (profile : ContradictionProfile M) : Prop :=
  Or (Not profile.domainApplies)
    (Or (Not profile.incompatibilityDetected)
      (Or (Not profile.sameScope)
        (Or (Not profile.sameContext) (Not profile.unresolved))))

theorem contradiction_domain_failure_blocks_profile {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : Not profile.domainApplies) :
    ContradictionProfileBlocked profile :=
  Or.inl h

theorem no_incompatibility_blocks_profile {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : Not profile.incompatibilityDetected) :
    ContradictionProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem scope_mismatch_blocks_contradiction_profile {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : Not profile.sameScope) :
    ContradictionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem context_mismatch_blocks_contradiction_profile {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : Not profile.sameContext) :
    ContradictionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem resolved_status_blocks_contradiction_profile {M : SigmaModel}
    (profile : ContradictionProfile M)
    (h : Not profile.unresolved) :
    ContradictionProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

def LogicalContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.logical }

def SemanticContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.semantic }

def PragmaticContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.pragmatic }

def NormativeContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.normative }

def InstitutionalContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.institutional }

def FrameConflictProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.frameConflict }

def SupportTreatmentContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.supportTreatment }

def SymbolicContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.symbolic }

def SacredContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.sacred }

def ResidueContradictionProfile (M : SigmaModel) : Type :=
  { p : ContradictionProfile M // p.kind = ContradictionKind.residue }

def logical_profile_to_case {M : SigmaModel}
    (p : LogicalContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    LogicalContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.logical
    exact p.property⟩

def semantic_profile_to_case {M : SigmaModel}
    (p : SemanticContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    SemanticContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.semantic
    exact p.property⟩

def support_treatment_profile_to_case {M : SigmaModel}
    (p : SupportTreatmentContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    SupportTreatmentContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.supportTreatment
    exact p.property⟩

def pragmatic_profile_to_case {M : SigmaModel}
    (p : PragmaticContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    PragmaticContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.pragmatic
    exact p.property⟩

def normative_profile_to_case {M : SigmaModel}
    (p : NormativeContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    NormativeContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.normative
    exact p.property⟩

def institutional_profile_to_case {M : SigmaModel}
    (p : InstitutionalContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    InstitutionalContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.institutional
    exact p.property⟩

def frame_conflict_profile_to_case {M : SigmaModel}
    (p : FrameConflictProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    FrameConflictCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.frameConflict
    exact p.property⟩

def symbolic_profile_to_case {M : SigmaModel}
    (p : SymbolicContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    SymbolicContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.symbolic
    exact p.property⟩

def sacred_profile_to_case {M : SigmaModel}
    (p : SacredContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    SacredContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.sacred
    exact p.property⟩

def residue_profile_to_case {M : SigmaModel}
    (p : ResidueContradictionProfile M)
    (h : ContradictionProfileSatisfied p.val) :
    ResidueContradictionCase M :=
  ⟨ContradictionProfile.toCase p.val h, by
    change p.val.kind = ContradictionKind.residue
    exact p.property⟩

def contradictionOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.contradictionPresent => True
  | _ => False

def contradictionOnlyModel : SigmaModel :=
  UnitPredicateModel contradictionOnlyTruth

def contradictionOnlyCase : ContradictionCase contradictionOnlyModel :=
  { kind := ContradictionKind.logical
    frame := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    present := True.intro }

def contradictionOnlyProfile (kind : ContradictionKind) :
    ContradictionProfile contradictionOnlyModel :=
  { kind := kind
    frame := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    domainApplies := True
    incompatibilityDetected := True
    sameScope := True
    sameContext := True
    unresolved := True
    warrant := by
      intro _ _ _ _ _
      exact True.intro }

theorem contradictionOnlyProfile_satisfied (kind : ContradictionKind) :
    ContradictionProfileSatisfied (contradictionOnlyProfile kind) :=
  { domainApplies := True.intro
    incompatibilityDetected := True.intro
    sameScope := True.intro
    sameContext := True.intro
    unresolved := True.intro }

def logicalContradictionOnlyProfile :
    LogicalContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.logical, rfl⟩

def semanticContradictionOnlyProfile :
    SemanticContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.semantic, rfl⟩

def pragmaticContradictionOnlyProfile :
    PragmaticContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.pragmatic, rfl⟩

def normativeContradictionOnlyProfile :
    NormativeContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.normative, rfl⟩

def institutionalContradictionOnlyProfile :
    InstitutionalContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.institutional, rfl⟩

def frameConflictOnlyProfile :
    FrameConflictProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.frameConflict, rfl⟩

def supportTreatmentContradictionOnlyProfile :
    SupportTreatmentContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.supportTreatment, rfl⟩

def symbolicContradictionOnlyProfile :
    SymbolicContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.symbolic, rfl⟩

def sacredContradictionOnlyProfile :
    SacredContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.sacred, rfl⟩

def residueContradictionOnlyProfile :
    ResidueContradictionProfile contradictionOnlyModel :=
  ⟨contradictionOnlyProfile ContradictionKind.residue, rfl⟩

theorem contradictionOnly_has_contradiction :
    ContradictionPresentSem (M := contradictionOnlyModel) Unit.unit Unit.unit
      Unit.unit :=
  True.intro

theorem contradictionOnly_not_ValidInsightSem :
    Not (ValidInsightSem contradictionOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem contradictionOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem contradictionOnlyModel Unit.unit
      Unit.unit) := by
  intro h
  exact h.validation

theorem contradictionOnly_not_HarmBridgeSem :
    Not (HarmBridgeSem (M := contradictionOnlyModel) Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem contradictionOnly_not_MoralGuiltBridgeSem :
    Not (MoralGuiltBridgeSem (M := contradictionOnlyModel) Unit.unit
      Unit.unit) := by
  intro h
  exact h

theorem contradictionOnly_not_RepairObligationBridgeSem :
    Not (RepairObligationBridgeSem (M := contradictionOnlyModel) Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h

def contradictionAndCollapseTruth : PredicateSymbol -> Prop
  | PredicateSymbol.contradictionPresent => True
  | _ => False

def contradictionNoCollapseModel : SigmaModel :=
  UnitPredicateModel contradictionAndCollapseTruth

theorem contradictionNoCollapse_has_contradiction :
    ContradictionPresentSem (M := contradictionNoCollapseModel) Unit.unit
      Unit.unit Unit.unit :=
  True.intro

theorem contradictionNoCollapse_not_directional_change :
    Not (DirectionalNonEquivalenceSem (M := contradictionNoCollapseModel)
      Unit.unit Unit.unit) := by
  intro h
  exact h

theorem satisfied_profile_not_necessarily_valid_insight
    (kind : ContradictionKind) :
    ContradictionProfileSatisfied (contradictionOnlyProfile kind) ∧
    Not (ValidInsightSem contradictionOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) :=
  And.intro (contradictionOnlyProfile_satisfied kind)
    contradictionOnly_not_ValidInsightSem

theorem satisfied_profile_not_necessarily_empirical_validation
    (kind : ContradictionKind) :
    ContradictionProfileSatisfied (contradictionOnlyProfile kind) ∧
    Not (FullEmpiricalValidationSem contradictionOnlyModel Unit.unit
      Unit.unit) :=
  And.intro (contradictionOnlyProfile_satisfied kind)
    contradictionOnly_not_FullEmpiricalValidationSem

theorem satisfied_profile_not_necessarily_moral_guilt
    (kind : ContradictionKind) :
    ContradictionProfileSatisfied (contradictionOnlyProfile kind) ∧
    Not (MoralGuiltBridgeSem (M := contradictionOnlyModel) Unit.unit
      Unit.unit) :=
  And.intro (contradictionOnlyProfile_satisfied kind)
    contradictionOnly_not_MoralGuiltBridgeSem

end Paralogic
