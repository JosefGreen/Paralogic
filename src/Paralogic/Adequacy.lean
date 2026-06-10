import Paralogic.ModelSemantics

/-!
Domain adequacy calculus.

ISFT depends on claims about support adequacy.  This module makes adequacy
domain-relative and condition-gated, so "inadequate support" is not a free
standing rhetorical label.
-/

namespace Paralogic

inductive AdequacyDomain where
  | logical
  | empirical
  | legal
  | governance
  | moral
  | institutional
  | narrative
  | technical
  deriving DecidableEq, Repr

structure AdequacyProfile (M : SigmaModel) where
  domain : AdequacyDomain
  evidence : M.Carrier SortTag.evidenceSet
  context : M.Carrier SortTag.context
  claim : M.Carrier SortTag.claim
  relevant : Prop
  sufficient : Prop
  current : Prop
  methodologicallyFit : Prop
  uncertaintyBounded : Prop
  scopeMatched : Prop
  warrant :
    relevant ->
    sufficient ->
    current ->
    methodologicallyFit ->
    uncertaintyBounded ->
    scopeMatched ->
    M.interpPredicate PredicateSymbol.adequate
      (Args.cons evidence (Args.cons context (Args.cons claim Args.nil)))

def AdequacyProfileSatisfied {M : SigmaModel}
    (profile : AdequacyProfile M) : Prop :=
  And profile.relevant
    (And profile.sufficient
      (And profile.current
        (And profile.methodologicallyFit
          (And profile.uncertaintyBounded profile.scopeMatched))))

theorem AdequacyProfile_to_AdequateSem {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : AdequacyProfileSatisfied profile) :
    M.interpPredicate PredicateSymbol.adequate
      (Args.cons profile.evidence
        (Args.cons profile.context (Args.cons profile.claim Args.nil))) :=
  profile.warrant h.left h.right.left h.right.right.left
    h.right.right.right.left h.right.right.right.right.left
    h.right.right.right.right.right

def AdequacyProfileBlocked {M : SigmaModel}
    (profile : AdequacyProfile M) : Prop :=
  Or (Not profile.relevant)
    (Or (Not profile.sufficient)
      (Or (Not profile.current)
        (Or (Not profile.methodologicallyFit)
          (Or (Not profile.uncertaintyBounded)
            (Not profile.scopeMatched)))))

theorem irrelevance_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.relevant) :
    AdequacyProfileBlocked profile :=
  Or.inl h

theorem insufficiency_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.sufficient) :
    AdequacyProfileBlocked profile :=
  Or.inr (Or.inl h)

theorem stale_support_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.current) :
    AdequacyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem method_mismatch_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.methodologicallyFit) :
    AdequacyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem unbounded_uncertainty_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.uncertaintyBounded) :
    AdequacyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem scope_mismatch_blocks_adequacy {M : SigmaModel}
    (profile : AdequacyProfile M)
    (h : Not profile.scopeMatched) :
    AdequacyProfileBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Paralogic
