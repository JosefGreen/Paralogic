import Paralogic.ModelSemantics

/-!
Empirical validation boundary schemas.

Formal definitions and machine checks do not establish empirical validity.
This module requires empirical-validation claims to pass explicit protocol
conditions before they count as full validation in the formal model.
-/

namespace Paralogic

structure EmpiricalValidationProtocol (M : SigmaModel) where
  validationObject : M.Carrier SortTag.empiricalValidationObject
  targetClaim : M.Carrier SortTag.claim
  operationalized : Prop
  constructBoundaryDeclared : Prop
  constructValid : Prop
  reliabilityTested : Prop
  externalReplicationAvailable : Prop
  domainScopeDeclared : Prop
  limitationsDeclared : Prop
  warrant :
    operationalized ->
    constructBoundaryDeclared ->
    constructValid ->
    reliabilityTested ->
    externalReplicationAvailable ->
    domainScopeDeclared ->
    limitationsDeclared ->
    FullEmpiricalValidationSem M validationObject targetClaim

def EmpiricalProtocolApplies {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M) : Prop :=
  And protocol.operationalized
    (And protocol.constructBoundaryDeclared
      (And protocol.constructValid
        (And protocol.reliabilityTested
          (And protocol.externalReplicationAvailable
            (And protocol.domainScopeDeclared protocol.limitationsDeclared)))))

theorem EmpiricalValidationProtocol_to_full_validation {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M)
    (h : EmpiricalProtocolApplies protocol) :
    FullEmpiricalValidationSem M protocol.validationObject
      protocol.targetClaim :=
  protocol.warrant h.left h.right.left h.right.right.left
    h.right.right.right.left h.right.right.right.right.left
    h.right.right.right.right.right.left h.right.right.right.right.right.right

def EmpiricalProtocolBlocked {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M) : Prop :=
  Or (Not protocol.operationalized)
    (Or (Not protocol.constructBoundaryDeclared)
      (Or (Not protocol.constructValid)
        (Or (Not protocol.reliabilityTested)
          (Or (Not protocol.externalReplicationAvailable)
            (Or (Not protocol.domainScopeDeclared)
              (Not protocol.limitationsDeclared))))))

theorem no_operationalization_blocks_empirical_protocol {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M)
    (h : Not protocol.operationalized) :
    EmpiricalProtocolBlocked protocol :=
  Or.inl h

theorem no_construct_validity_blocks_empirical_protocol {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M)
    (h : Not protocol.constructValid) :
    EmpiricalProtocolBlocked protocol :=
  Or.inr (Or.inr (Or.inl h))

theorem no_reliability_blocks_empirical_protocol {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M)
    (h : Not protocol.reliabilityTested) :
    EmpiricalProtocolBlocked protocol :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem no_replication_blocks_empirical_protocol {M : SigmaModel}
    (protocol : EmpiricalValidationProtocol M)
    (h : Not protocol.externalReplicationAvailable) :
    EmpiricalProtocolBlocked protocol :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

end Paralogic
