import Paralogic.Adequacy

/-!
Rough evidence approximations.

This module starts the rough-set novelty lane.  It separates definite support
from possible support under an indiscernibility relation, and isolates boundary
cases where support is possible but not definite.
-/

namespace Paralogic

structure RoughEvidenceSpace : Type 1 where
  Obj : Type
  indistinguishable : Obj -> Obj -> Prop
  supports : Obj -> Prop
  reflexive : forall item : Obj, indistinguishable item item

def LowerApprox (space : RoughEvidenceSpace)
    (item : space.Obj) : Prop :=
  And (space.supports item)
    (forall other : space.Obj,
      space.indistinguishable item other -> space.supports other)

def UpperApprox (space : RoughEvidenceSpace)
    (item : space.Obj) : Prop :=
  Exists (fun other : space.Obj =>
    And (space.indistinguishable item other) (space.supports other))

def BoundaryRegion (space : RoughEvidenceSpace)
    (item : space.Obj) : Prop :=
  And (UpperApprox space item) (Not (LowerApprox space item))

theorem lower_implies_upper
    (space : RoughEvidenceSpace)
    (item : space.Obj)
    (hLower : LowerApprox space item) :
    UpperApprox space item :=
  Exists.intro item (And.intro (space.reflexive item) hLower.left)

theorem boundary_implies_possible
    (space : RoughEvidenceSpace)
    (item : space.Obj)
    (hBoundary : BoundaryRegion space item) :
    UpperApprox space item :=
  hBoundary.left

theorem boundary_not_definite
    (space : RoughEvidenceSpace)
    (item : space.Obj)
    (hBoundary : BoundaryRegion space item) :
    Not (LowerApprox space item) :=
  hBoundary.right

inductive TwoEvidence where
  | favorable
  | unfavorable
  deriving DecidableEq, Repr

def twoEvidenceIndistinguishable
    (_left _right : TwoEvidence) : Prop :=
  True

def twoEvidenceSupports : TwoEvidence -> Prop
  | TwoEvidence.favorable => True
  | TwoEvidence.unfavorable => False

def twoEvidenceSpace : RoughEvidenceSpace :=
  { Obj := TwoEvidence
    indistinguishable := twoEvidenceIndistinguishable
    supports := twoEvidenceSupports
    reflexive := fun _ => True.intro }

theorem twoEvidence_favorable_upper :
    UpperApprox twoEvidenceSpace TwoEvidence.favorable :=
  Exists.intro TwoEvidence.favorable
    (And.intro True.intro True.intro)

theorem twoEvidence_favorable_not_lower :
    Not (LowerApprox twoEvidenceSpace TwoEvidence.favorable) := by
  intro hLower
  exact hLower.right TwoEvidence.unfavorable True.intro

theorem twoEvidence_favorable_boundary :
    BoundaryRegion twoEvidenceSpace TwoEvidence.favorable :=
  And.intro twoEvidence_favorable_upper twoEvidence_favorable_not_lower

theorem twoEvidence_unfavorable_upper :
    UpperApprox twoEvidenceSpace TwoEvidence.unfavorable :=
  Exists.intro TwoEvidence.favorable
    (And.intro True.intro True.intro)

theorem twoEvidence_unfavorable_not_lower :
    Not (LowerApprox twoEvidenceSpace TwoEvidence.unfavorable) := by
  intro hLower
  exact hLower.left

theorem twoEvidence_unfavorable_boundary :
    BoundaryRegion twoEvidenceSpace TwoEvidence.unfavorable :=
  And.intro twoEvidence_unfavorable_upper twoEvidence_unfavorable_not_lower

def RoughAdequacyEligible (space : RoughEvidenceSpace)
    (item : space.Obj) : Prop :=
  LowerApprox space item

theorem boundary_blocks_rough_adequacy
    (space : RoughEvidenceSpace)
    (item : space.Obj)
    (hBoundary : BoundaryRegion space item) :
    Not (RoughAdequacyEligible space item) :=
  hBoundary.right

theorem upper_not_necessarily_rough_adequacy :
    And (UpperApprox twoEvidenceSpace TwoEvidence.favorable)
      (Not (RoughAdequacyEligible twoEvidenceSpace TwoEvidence.favorable)) :=
  And.intro twoEvidence_favorable_upper
    (boundary_blocks_rough_adequacy twoEvidenceSpace TwoEvidence.favorable
      twoEvidence_favorable_boundary)

end Paralogic
