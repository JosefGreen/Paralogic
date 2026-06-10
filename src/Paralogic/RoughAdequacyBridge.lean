import Paralogic.RoughEvidence

/-!
Bridge from rough evidence to adequacy profiles.

This module connects the rough-set evidence layer to the existing adequacy
profile calculus.  It proves that if an adequacy profile treats sufficiency as
rough lower approximation, then boundary evidence cannot satisfy that
adequacy profile.
-/

namespace Paralogic

structure RoughAdequacyLink (M : SigmaModel) where
  space : RoughEvidenceSpace
  item : space.Obj
  profile : AdequacyProfile M
  sufficientIffLower :
    Iff profile.sufficient (LowerApprox space item)

theorem rough_lower_from_profile_sufficient {M : SigmaModel}
    (link : RoughAdequacyLink M)
    (hSufficient : link.profile.sufficient) :
    LowerApprox link.space link.item :=
  link.sufficientIffLower.mp hSufficient

theorem profile_sufficient_from_rough_lower {M : SigmaModel}
    (link : RoughAdequacyLink M)
    (hLower : LowerApprox link.space link.item) :
    link.profile.sufficient :=
  link.sufficientIffLower.mpr hLower

theorem rough_boundary_blocks_profile_satisfaction {M : SigmaModel}
    (link : RoughAdequacyLink M)
    (hBoundary : BoundaryRegion link.space link.item) :
    Not (AdequacyProfileSatisfied link.profile) := by
  intro hSatisfied
  exact hBoundary.right
    (rough_lower_from_profile_sufficient link hSatisfied.right.left)

theorem rough_boundary_blocks_profile {M : SigmaModel}
    (link : RoughAdequacyLink M)
    (hBoundary : BoundaryRegion link.space link.item) :
    AdequacyProfileBlocked link.profile :=
  insufficiency_blocks_adequacy link.profile
    (fun hSufficient =>
      hBoundary.right
        (rough_lower_from_profile_sufficient link hSufficient))

def roughBoundaryAdequacyModel : SigmaModel :=
  UnitPredicateModel (fun _ => False)

def roughBoundaryAdequacyProfile :
    AdequacyProfile roughBoundaryAdequacyModel :=
  { domain := AdequacyDomain.empirical
    evidence := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    relevant := True
    sufficient := LowerApprox twoEvidenceSpace TwoEvidence.favorable
    current := True
    methodologicallyFit := True
    uncertaintyBounded := True
    scopeMatched := True
    warrant := fun _ hSufficient _ _ _ _ =>
      False.elim (twoEvidence_favorable_not_lower hSufficient) }

def roughBoundaryAdequacyLink :
    RoughAdequacyLink roughBoundaryAdequacyModel :=
  { space := twoEvidenceSpace
    item := TwoEvidence.favorable
    profile := roughBoundaryAdequacyProfile
    sufficientIffLower := Iff.rfl }

theorem roughBoundaryAdequacyProfile_blocked :
    AdequacyProfileBlocked roughBoundaryAdequacyProfile :=
  rough_boundary_blocks_profile roughBoundaryAdequacyLink
    twoEvidence_favorable_boundary

theorem roughBoundaryAdequacyProfile_not_satisfied :
    Not (AdequacyProfileSatisfied roughBoundaryAdequacyProfile) :=
  rough_boundary_blocks_profile_satisfaction roughBoundaryAdequacyLink
    twoEvidence_favorable_boundary

end Paralogic
