import Paralogic.ModelSemantics
import Paralogic.Adequacy

/-!
M8 power-erasure semantics.

M8 is a power-erasure support failure, not a conclusion about oppression,
discrimination, harm, legal status, or guilt.  This module expands the
conditions under which the M8 predicate may be warranted while keeping
normative bridge conclusions separate.
-/

namespace Paralogic

inductive PowerDimension where
  | authority
  | resourceControl
  | categoryControl
  | metricControl
  | agendaControl
  | enforcementCapacity
  | vetoPower
  | visibilityControl
  deriving DecidableEq, Repr

structure PowerConditionProfile (M : SigmaModel) where
  institution : M.Carrier SortTag.institution
  output : M.Carrier SortTag.symbolicOutput
  condition : M.Carrier SortTag.powerCondition
  group : M.Carrier SortTag.affectedGroup
  dimension : PowerDimension
  relevantToClaimValidity : Prop
  omittedFromRepresentation : Prop
  omissionMaterial : Prop
  affectedGroupMaterial : Prop
  disclosureAbsent : Prop
  mitigationAbsent : Prop
  warrantRelevant :
    relevantToClaimValidity ->
    M.interpPredicate PredicateSymbol.powerRelevant
      (Args.cons institution (Args.cons group Args.nil))
  warrantDependence :
    relevantToClaimValidity ->
    M.interpPredicate PredicateSymbol.powerValidityDependence
      (Args.cons institution (Args.cons output (Args.cons condition Args.nil)))
  warrantOmission :
    omittedFromRepresentation ->
    omissionMaterial ->
    M.interpPredicate PredicateSymbol.powerOmitted
      (Args.cons institution (Args.cons output (Args.cons condition Args.nil)))

structure PowerConditionProfileSatisfied {M : SigmaModel}
    (profile : PowerConditionProfile M) : Prop where
  relevantToClaimValidity : profile.relevantToClaimValidity
  omittedFromRepresentation : profile.omittedFromRepresentation
  omissionMaterial : profile.omissionMaterial
  affectedGroupMaterial : profile.affectedGroupMaterial
  disclosureAbsent : profile.disclosureAbsent
  mitigationAbsent : profile.mitigationAbsent

theorem PowerConditionProfile_to_powerRelevant {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : PowerConditionProfileSatisfied profile) :
    PowerRelevantSem profile.institution profile.group :=
  profile.warrantRelevant h.relevantToClaimValidity

theorem PowerConditionProfile_to_powerValidityDependence {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : PowerConditionProfileSatisfied profile) :
    PowerValidityDependenceSem profile.institution profile.output
      profile.condition :=
  profile.warrantDependence h.relevantToClaimValidity

theorem PowerConditionProfile_to_powerOmitted {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : PowerConditionProfileSatisfied profile) :
    PowerOmittedSem profile.institution profile.output profile.condition :=
  profile.warrantOmission h.omittedFromRepresentation h.omissionMaterial

structure M8PowerErasureCase (M : SigmaModel) where
  claim : M.Carrier SortTag.claim
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  powerProfile : PowerConditionProfile M
  uses : UsesSem powerProfile.institution powerProfile.output
  claims : ClaimsSem powerProfile.institution powerProfile.output claim
  supportDegraded : SupportDegradedSem evidence context claim
  treatsAsAdequate :
    TreatsAsAdequateSem powerProfile.institution powerProfile.output claim
      context

structure M8PowerErasureSatisfied {M : SigmaModel}
    (caseData : M8PowerErasureCase M) : Prop where
  powerProfileSatisfied :
    PowerConditionProfileSatisfied caseData.powerProfile

theorem M8PowerErasureCase_to_M8Sem {M : SigmaModel}
    (caseData : M8PowerErasureCase M)
    (h : M8PowerErasureSatisfied caseData) :
    M8Sem M caseData.powerProfile.institution caseData.powerProfile.output
      caseData.claim caseData.evidence caseData.context
      caseData.powerProfile.condition caseData.powerProfile.group :=
  { uses := caseData.uses
    claims := caseData.claims
    powerRelevant :=
      PowerConditionProfile_to_powerRelevant caseData.powerProfile
        h.powerProfileSatisfied
    powerValidityDependence :=
      PowerConditionProfile_to_powerValidityDependence caseData.powerProfile
        h.powerProfileSatisfied
    powerOmitted :=
      PowerConditionProfile_to_powerOmitted caseData.powerProfile
        h.powerProfileSatisfied
    supportDegraded := caseData.supportDegraded
    treatsAsAdequate := caseData.treatsAsAdequate }

def PowerProfileBlocked {M : SigmaModel}
    (profile : PowerConditionProfile M) : Prop :=
  Or (Not profile.relevantToClaimValidity)
    (Or (Not profile.omittedFromRepresentation)
      (Or (Not profile.omissionMaterial)
        (Or (Not profile.affectedGroupMaterial)
          (Or (Not profile.disclosureAbsent) (Not profile.mitigationAbsent)))))

theorem irrelevant_power_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.relevantToClaimValidity) :
    PowerProfileBlocked profile :=
  Or.inl h

theorem represented_power_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.omittedFromRepresentation) :
    PowerProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem immaterial_omission_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.omissionMaterial) :
    PowerProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem immaterial_affected_group_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.affectedGroupMaterial) :
    PowerProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem disclosed_power_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.disclosureAbsent) :
    PowerProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem mitigated_power_blocks_profile {M : SigmaModel}
    (profile : PowerConditionProfile M)
    (h : Not profile.mitigationAbsent) :
    PowerProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Paralogic
