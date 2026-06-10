import Paralogic.ModelSemantics

/-!
Normative bridge schemas.

ISF and M8 are formal diagnostic predicates.  This module keeps normative
conclusions separate by requiring explicit bridge schemas with premises,
scope, defeater conditions, and a warrant from those conditions to the
normative conclusion.
-/

namespace Paralogic

inductive NormativeConclusion where
  | harm
  | responsibility
  | repairObligation
  | accountability
  | legalIllegitimacy
  | governanceLegitimacy
  | moralGuilt
  deriving DecidableEq, Repr

def NormativeConclusionSem {M : SigmaModel}
    (conclusion : NormativeConclusion)
    (bridge : M.Carrier SortTag.normativeBridge)
    (institution : M.Carrier SortTag.institution)
    (group : M.Carrier SortTag.affectedGroup) : Prop :=
  match conclusion with
  | NormativeConclusion.harm =>
      M.interpPredicate PredicateSymbol.harmBridge
        (Args.cons bridge (Args.cons institution (Args.cons group Args.nil)))
  | NormativeConclusion.responsibility =>
      M.interpPredicate PredicateSymbol.responsibilityBridge
        (Args.cons bridge (Args.cons institution Args.nil))
  | NormativeConclusion.repairObligation =>
      M.interpPredicate PredicateSymbol.repairObligationBridge
        (Args.cons bridge (Args.cons institution (Args.cons group Args.nil)))
  | NormativeConclusion.accountability =>
      M.interpPredicate PredicateSymbol.accountabilityBridge
        (Args.cons bridge (Args.cons institution Args.nil))
  | NormativeConclusion.legalIllegitimacy =>
      M.interpPredicate PredicateSymbol.legalIllegitimacyBridge
        (Args.cons bridge (Args.cons institution Args.nil))
  | NormativeConclusion.governanceLegitimacy =>
      M.interpPredicate PredicateSymbol.governanceLegitimacyBridge
        (Args.cons bridge (Args.cons institution Args.nil))
  | NormativeConclusion.moralGuilt =>
      M.interpPredicate PredicateSymbol.moralGuiltBridge
        (Args.cons bridge (Args.cons institution Args.nil))

structure NormativeBridgeSchema (M : SigmaModel) where
  conclusion : NormativeConclusion
  bridge : M.Carrier SortTag.normativeBridge
  institution : M.Carrier SortTag.institution
  group : M.Carrier SortTag.affectedGroup
  premisesSatisfied : Prop
  scopeApplies : Prop
  defeatersAbsent : Prop
  warrant :
    premisesSatisfied ->
    scopeApplies ->
    defeatersAbsent ->
    NormativeConclusionSem conclusion bridge institution group

def BridgeApplies {M : SigmaModel} (schema : NormativeBridgeSchema M) : Prop :=
  And schema.premisesSatisfied
    (And schema.scopeApplies schema.defeatersAbsent)

theorem NormativeBridgeSchema_to_conclusion {M : SigmaModel}
    (schema : NormativeBridgeSchema M)
    (h : BridgeApplies schema) :
    NormativeConclusionSem schema.conclusion schema.bridge schema.institution
      schema.group :=
  schema.warrant h.left h.right.left h.right.right

def BridgeDoesNotApply {M : SigmaModel}
    (schema : NormativeBridgeSchema M) : Prop :=
  Or (Not schema.premisesSatisfied)
    (Or (Not schema.scopeApplies) (Not schema.defeatersAbsent))

theorem missing_premise_blocks_bridge {M : SigmaModel}
    (schema : NormativeBridgeSchema M)
    (h : Not schema.premisesSatisfied) :
    BridgeDoesNotApply schema :=
  Or.inl h

theorem scope_failure_blocks_bridge {M : SigmaModel}
    (schema : NormativeBridgeSchema M)
    (h : Not schema.scopeApplies) :
    BridgeDoesNotApply schema :=
  Or.inr (Or.inl h)

theorem defeater_blocks_bridge {M : SigmaModel}
    (schema : NormativeBridgeSchema M)
    (h : Not schema.defeatersAbsent) :
    BridgeDoesNotApply schema :=
  Or.inr (Or.inr h)

def conclusionPredicate : NormativeConclusion -> PredicateSymbol
  | NormativeConclusion.harm => PredicateSymbol.harmBridge
  | NormativeConclusion.responsibility => PredicateSymbol.responsibilityBridge
  | NormativeConclusion.repairObligation =>
      PredicateSymbol.repairObligationBridge
  | NormativeConclusion.accountability => PredicateSymbol.accountabilityBridge
  | NormativeConclusion.legalIllegitimacy =>
      PredicateSymbol.legalIllegitimacyBridge
  | NormativeConclusion.governanceLegitimacy =>
      PredicateSymbol.governanceLegitimacyBridge
  | NormativeConclusion.moralGuilt => PredicateSymbol.moralGuiltBridge

def conclusionOnlyTruth (conclusion : NormativeConclusion)
    (predicate : PredicateSymbol) : Prop :=
  predicate = conclusionPredicate conclusion

def conclusionOnlyModel (conclusion : NormativeConclusion) : SigmaModel :=
  UnitPredicateModel (conclusionOnlyTruth conclusion)

def conclusionOnlySchema (conclusion : NormativeConclusion) :
    NormativeBridgeSchema (conclusionOnlyModel conclusion) :=
  { conclusion := conclusion
    bridge := Unit.unit
    institution := Unit.unit
    group := Unit.unit
    premisesSatisfied := True
    scopeApplies := True
    defeatersAbsent := True
    warrant := by
      intro _premises _scope _defeaters
      cases conclusion <;> rfl }

theorem conclusionOnlySchema_applies
    (conclusion : NormativeConclusion) :
    BridgeApplies (conclusionOnlySchema conclusion) :=
  And.intro True.intro (And.intro True.intro True.intro)

theorem conclusionOnlySchema_to_sem
    (conclusion : NormativeConclusion) :
    NormativeConclusionSem (M := conclusionOnlyModel conclusion)
      conclusion Unit.unit Unit.unit Unit.unit :=
  NormativeBridgeSchema_to_conclusion (conclusionOnlySchema conclusion)
    (conclusionOnlySchema_applies conclusion)

theorem harm_schema_to_sem :
    NormativeConclusionSem (M := conclusionOnlyModel NormativeConclusion.harm)
      NormativeConclusion.harm Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.harm

theorem responsibility_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.responsibility)
      NormativeConclusion.responsibility Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.responsibility

theorem repair_obligation_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.repairObligation)
      NormativeConclusion.repairObligation Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.repairObligation

theorem accountability_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.accountability)
      NormativeConclusion.accountability Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.accountability

theorem legal_illegitimacy_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.legalIllegitimacy)
      NormativeConclusion.legalIllegitimacy Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.legalIllegitimacy

theorem governance_legitimacy_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.governanceLegitimacy)
      NormativeConclusion.governanceLegitimacy Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.governanceLegitimacy

theorem moral_guilt_schema_to_sem :
    NormativeConclusionSem
      (M := conclusionOnlyModel NormativeConclusion.moralGuilt)
      NormativeConclusion.moralGuilt Unit.unit Unit.unit Unit.unit :=
  conclusionOnlySchema_to_sem NormativeConclusion.moralGuilt

end Paralogic
