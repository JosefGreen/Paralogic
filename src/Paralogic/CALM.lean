/-!
CALM: Capability Assurance and Learning Mobility.

This module gives the Paper Armies / CALM workstream a small checked core for
claim travel, learning travel, and reflexivity. It is an operational guard
schema, not empirical validation and not a claim that CALM is complete.
-/

namespace Paralogic

namespace CALM

inductive ClaimKind where
  | readiness
  | interoperability
  | aiEnabled
  | authorization
  | sustainment
  | learning
  | metric
  | publicNarrative
  deriving DecidableEq, Repr

inductive WarrantMaturity where
  | assertedOnly
  | operationallyModeled
  | sourceBacked
  | empiricallyValidated
  | independentlyReviewed
  | replicated
  deriving DecidableEq, Repr

inductive LearningBarrier where
  | discovery
  | classification
  | cyberAuthorization
  | dataRights
  | funding
  | contracting
  | training
  | sustainment
  | ownership
  | timing
  deriving DecidableEq, Repr

structure ClaimReceipt where
  claimKind : ClaimKind
  evidenceOffered : Prop
  boundaryDeclared : Prop
  negativeSpaceDeclared : Prop
  consequenceOwnerDeclared : Prop
  expirationDeclared : Prop
  operationalValidityDemonstrated : Prop
  impliesOperationalValidity : Prop

def ClaimTravelReady (receipt : ClaimReceipt) : Prop :=
  receipt.evidenceOffered
    ∧ receipt.boundaryDeclared
    ∧ receipt.negativeSpaceDeclared
    ∧ receipt.consequenceOwnerDeclared
    ∧ receipt.expirationDeclared

def PaperCapabilityRisk (receipt : ClaimReceipt) : Prop :=
  receipt.impliesOperationalValidity ∧
    Not receipt.operationalValidityDemonstrated

theorem missing_evidence_blocks_claim_travel {receipt : ClaimReceipt}
    (h : Not receipt.evidenceOffered) :
    Not (ClaimTravelReady receipt) := by
  intro ready
  exact h ready.1

theorem missing_boundary_blocks_claim_travel {receipt : ClaimReceipt}
    (h : Not receipt.boundaryDeclared) :
    Not (ClaimTravelReady receipt) := by
  intro ready
  exact h ready.2.1

theorem missing_negative_space_blocks_claim_travel {receipt : ClaimReceipt}
    (h : Not receipt.negativeSpaceDeclared) :
    Not (ClaimTravelReady receipt) := by
  intro ready
  exact h ready.2.2.1

theorem missing_consequence_owner_blocks_claim_travel {receipt : ClaimReceipt}
    (h : Not receipt.consequenceOwnerDeclared) :
    Not (ClaimTravelReady receipt) := by
  intro ready
  exact h ready.2.2.2.1

theorem missing_expiration_blocks_claim_travel {receipt : ClaimReceipt}
    (h : Not receipt.expirationDeclared) :
    Not (ClaimTravelReady receipt) := by
  intro ready
  exact h ready.2.2.2.2

theorem paper_capability_risk_not_operational_validity
    {receipt : ClaimReceipt} (h : PaperCapabilityRisk receipt) :
    Not receipt.operationalValidityDemonstrated :=
  h.2

theorem claim_travel_ready_does_not_prove_operational_validity :
    Not (∀ receipt : ClaimReceipt,
      ClaimTravelReady receipt -> receipt.operationalValidityDemonstrated) := by
  intro h
  let weakReceipt : ClaimReceipt :=
    { claimKind := ClaimKind.readiness
      evidenceOffered := True
      boundaryDeclared := True
      negativeSpaceDeclared := True
      consequenceOwnerDeclared := True
      expirationDeclared := True
      operationalValidityDemonstrated := False
      impliesOperationalValidity := True }
  have ready : ClaimTravelReady weakReceipt := by
    repeat constructor
  exact h weakReceipt ready

structure LearningPacket where
  localUseDescribed : Prop
  conditionsDeclared : Prop
  receiverIdentified : Prop
  reuseBarriersLogged : Prop
  stewardshipOwnerDeclared : Prop
  secondUsePlanDeclared : Prop
  secondValidUseObserved : Prop

def LearningTravelReady (packet : LearningPacket) : Prop :=
  packet.localUseDescribed
    ∧ packet.conditionsDeclared
    ∧ packet.receiverIdentified
    ∧ packet.reuseBarriersLogged
    ∧ packet.stewardshipOwnerDeclared
    ∧ packet.secondUsePlanDeclared

def InstitutionalLearningObserved (packet : LearningPacket) : Prop :=
  packet.secondValidUseObserved

theorem missing_receiver_blocks_learning_travel {packet : LearningPacket}
    (h : Not packet.receiverIdentified) :
    Not (LearningTravelReady packet) := by
  intro ready
  exact h ready.2.2.1

theorem missing_second_use_plan_blocks_learning_travel
    {packet : LearningPacket}
    (h : Not packet.secondUsePlanDeclared) :
    Not (LearningTravelReady packet) := by
  intro ready
  exact h ready.2.2.2.2.2

theorem learning_travel_ready_does_not_prove_second_valid_use :
    Not (∀ packet : LearningPacket,
      LearningTravelReady packet -> InstitutionalLearningObserved packet) := by
  intro h
  let plannedPacket : LearningPacket :=
    { localUseDescribed := True
      conditionsDeclared := True
      receiverIdentified := True
      reuseBarriersLogged := True
      stewardshipOwnerDeclared := True
      secondUsePlanDeclared := True
      secondValidUseObserved := False }
  have ready : LearningTravelReady plannedPacket := by
    repeat constructor
  exact h plannedPacket ready

structure CALMImplementation where
  artifactsCompleted : Prop
  decisionBoundaryChanged : Prop
  learningTransferred : Prop
  legacyBurdenReduced : Prop
  metricCanImproveWhileTruthWorsens : Prop

def ReflexivityPass (implementation : CALMImplementation) : Prop :=
  implementation.decisionBoundaryChanged
    ∨ implementation.learningTransferred
    ∨ implementation.legacyBurdenReduced

def PaperCALMRisk (implementation : CALMImplementation) : Prop :=
  implementation.artifactsCompleted
    ∧ Not implementation.decisionBoundaryChanged
    ∧ Not implementation.learningTransferred

theorem artifacts_alone_do_not_pass_reflexivity
    (implementation : CALMImplementation)
    (hDecision : Not implementation.decisionBoundaryChanged)
    (hLearning : Not implementation.learningTransferred)
    (hBurden : Not implementation.legacyBurdenReduced) :
    Not (ReflexivityPass implementation) := by
  intro hPass
  cases hPass with
  | inl hDecisionChanged =>
      exact hDecision hDecisionChanged
  | inr hRest =>
      cases hRest with
      | inl hLearningTransferred =>
          exact hLearning hLearningTransferred
      | inr hLegacyReduced =>
          exact hBurden hLegacyReduced

theorem paper_calm_risk_blocks_reflexivity_when_no_burden_reduction
    {implementation : CALMImplementation}
    (hRisk : PaperCALMRisk implementation)
    (hBurden : Not implementation.legacyBurdenReduced) :
    Not (ReflexivityPass implementation) :=
  artifacts_alone_do_not_pass_reflexivity implementation
    hRisk.2.1 hRisk.2.2 hBurden

end CALM

end Paralogic
