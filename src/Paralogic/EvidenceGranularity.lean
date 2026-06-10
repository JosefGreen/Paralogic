import Paralogic.RoughAdequacyBridge

/-!
Finite evidence-granularity tests.

This module checks that rough adequacy is sensitive to evidence granularity.
With the coarse two-item space from `RoughEvidence`, favorable evidence is
only boundary-level.  With identity-level granularity over the same objects,
the favorable item becomes a lower approximation and is therefore eligible for
rough adequacy.
-/

namespace Paralogic

def roughSpaceOf {Obj : Type}
    (relation : Obj -> Obj -> Prop)
    (supports : Obj -> Prop)
    (reflexive : forall item : Obj, relation item item) :
    RoughEvidenceSpace :=
  { Obj := Obj
    indistinguishable := relation
    supports := supports
    reflexive := reflexive }

theorem lower_preserved_under_relation_refinement
    {Obj : Type}
    (supports : Obj -> Prop)
    (coarse fine : Obj -> Obj -> Prop)
    (coarseReflexive : forall item : Obj, coarse item item)
    (fineReflexive : forall item : Obj, fine item item)
    (fineRefinesCoarse :
      forall left right : Obj, fine left right -> coarse left right)
    (item : Obj)
    (hLower :
      LowerApprox (roughSpaceOf coarse supports coarseReflexive) item) :
    LowerApprox (roughSpaceOf fine supports fineReflexive) item := by
  constructor
  case left =>
    exact hLower.left
  case right =>
    intro other hFine
    exact hLower.right other (fineRefinesCoarse item other hFine)

def fineTwoEvidenceIndistinguishable
    (left right : TwoEvidence) : Prop :=
  left = right

def fineTwoEvidenceSpace : RoughEvidenceSpace :=
  { Obj := TwoEvidence
    indistinguishable := fineTwoEvidenceIndistinguishable
    supports := twoEvidenceSupports
    reflexive := fun _ => rfl }

theorem fineTwoEvidence_favorable_lower :
    LowerApprox fineTwoEvidenceSpace TwoEvidence.favorable := by
  constructor
  case left =>
    exact True.intro
  case right =>
    intro other hSame
    cases hSame
    exact True.intro

theorem fineTwoEvidence_favorable_upper :
    UpperApprox fineTwoEvidenceSpace TwoEvidence.favorable :=
  lower_implies_upper fineTwoEvidenceSpace TwoEvidence.favorable
    fineTwoEvidence_favorable_lower

theorem fineTwoEvidence_favorable_not_boundary :
    Not (BoundaryRegion fineTwoEvidenceSpace TwoEvidence.favorable) := by
  intro hBoundary
  exact hBoundary.right fineTwoEvidence_favorable_lower

theorem fineTwoEvidence_favorable_eligible :
    RoughAdequacyEligible fineTwoEvidenceSpace TwoEvidence.favorable :=
  fineTwoEvidence_favorable_lower

theorem fineTwoEvidence_refines_coarse :
    forall left right : TwoEvidence,
      fineTwoEvidenceIndistinguishable left right ->
      twoEvidenceIndistinguishable left right :=
  fun _ _ _ => True.intro

theorem twoEvidence_coarse_lower_implies_fine_lower
    (item : TwoEvidence)
    (hLower : LowerApprox twoEvidenceSpace item) :
    LowerApprox fineTwoEvidenceSpace item :=
  lower_preserved_under_relation_refinement
    twoEvidenceSupports
    twoEvidenceIndistinguishable
    fineTwoEvidenceIndistinguishable
    (fun _ => True.intro)
    (fun _ => rfl)
    fineTwoEvidence_refines_coarse
    item
    hLower

theorem granularity_changes_favorable_adequacy :
    And
      (Not (RoughAdequacyEligible twoEvidenceSpace TwoEvidence.favorable))
      (RoughAdequacyEligible fineTwoEvidenceSpace TwoEvidence.favorable) :=
  And.intro
    (boundary_blocks_rough_adequacy twoEvidenceSpace TwoEvidence.favorable
      twoEvidence_favorable_boundary)
    fineTwoEvidence_favorable_eligible

theorem fine_lower_does_not_imply_coarse_lower :
    And
      (LowerApprox fineTwoEvidenceSpace TwoEvidence.favorable)
      (Not (LowerApprox twoEvidenceSpace TwoEvidence.favorable)) :=
  And.intro fineTwoEvidence_favorable_lower
    twoEvidence_favorable_not_lower

inductive ThreeEvidence where
  | favorable
  | corroborating
  | unfavorable
  deriving DecidableEq, Repr

def threeEvidenceSupports : ThreeEvidence -> Prop
  | ThreeEvidence.favorable => True
  | ThreeEvidence.corroborating => True
  | ThreeEvidence.unfavorable => False

def coarseThreeEvidenceIndistinguishable
    (_left _right : ThreeEvidence) : Prop :=
  True

def fineThreeEvidenceIndistinguishable
    (left right : ThreeEvidence) : Prop :=
  left = right

def coarseThreeEvidenceSpace : RoughEvidenceSpace :=
  { Obj := ThreeEvidence
    indistinguishable := coarseThreeEvidenceIndistinguishable
    supports := threeEvidenceSupports
    reflexive := fun _ => True.intro }

def fineThreeEvidenceSpace : RoughEvidenceSpace :=
  { Obj := ThreeEvidence
    indistinguishable := fineThreeEvidenceIndistinguishable
    supports := threeEvidenceSupports
    reflexive := fun _ => rfl }

theorem fineThreeEvidence_favorable_lower :
    LowerApprox fineThreeEvidenceSpace ThreeEvidence.favorable := by
  constructor
  case left =>
    exact True.intro
  case right =>
    intro other hSame
    cases hSame
    exact True.intro

theorem fineThreeEvidence_corroborating_lower :
    LowerApprox fineThreeEvidenceSpace ThreeEvidence.corroborating := by
  constructor
  case left =>
    exact True.intro
  case right =>
    intro other hSame
    cases hSame
    exact True.intro

theorem coarseThreeEvidence_favorable_not_lower :
    Not (LowerApprox coarseThreeEvidenceSpace ThreeEvidence.favorable) := by
  intro hLower
  exact hLower.right ThreeEvidence.unfavorable True.intro

theorem coarseThreeEvidence_corroborating_not_lower :
    Not (LowerApprox coarseThreeEvidenceSpace ThreeEvidence.corroborating) := by
  intro hLower
  exact hLower.right ThreeEvidence.unfavorable True.intro

theorem coarseThreeEvidence_favorable_upper :
    UpperApprox coarseThreeEvidenceSpace ThreeEvidence.favorable :=
  Exists.intro ThreeEvidence.favorable
    (And.intro True.intro True.intro)

theorem coarseThreeEvidence_favorable_boundary :
    BoundaryRegion coarseThreeEvidenceSpace ThreeEvidence.favorable :=
  And.intro coarseThreeEvidence_favorable_upper
    coarseThreeEvidence_favorable_not_lower

theorem fineThreeEvidence_refines_coarse :
    forall left right : ThreeEvidence,
      fineThreeEvidenceIndistinguishable left right ->
      coarseThreeEvidenceIndistinguishable left right :=
  fun _ _ _ => True.intro

theorem threeEvidence_coarse_lower_implies_fine_lower
    (item : ThreeEvidence)
    (hLower : LowerApprox coarseThreeEvidenceSpace item) :
    LowerApprox fineThreeEvidenceSpace item :=
  lower_preserved_under_relation_refinement
    threeEvidenceSupports
    coarseThreeEvidenceIndistinguishable
    fineThreeEvidenceIndistinguishable
    (fun _ => True.intro)
    (fun _ => rfl)
    fineThreeEvidence_refines_coarse
    item
    hLower

theorem threeEvidence_favorable_converse_failure :
    And
      (LowerApprox fineThreeEvidenceSpace ThreeEvidence.favorable)
      (Not (LowerApprox coarseThreeEvidenceSpace ThreeEvidence.favorable)) :=
  And.intro fineThreeEvidence_favorable_lower
    coarseThreeEvidence_favorable_not_lower

theorem threeEvidence_corroborating_converse_failure :
    And
      (LowerApprox fineThreeEvidenceSpace ThreeEvidence.corroborating)
      (Not (LowerApprox coarseThreeEvidenceSpace
        ThreeEvidence.corroborating)) :=
  And.intro fineThreeEvidence_corroborating_lower
    coarseThreeEvidence_corroborating_not_lower

structure ThreeGranularityMask where
  favorableToCorroborating : Bool
  favorableToUnfavorable : Bool
  corroboratingToFavorable : Bool
  corroboratingToUnfavorable : Bool
  unfavorableToFavorable : Bool
  unfavorableToCorroborating : Bool
  deriving DecidableEq, Repr

def ThreeGranularityMask.relation
    (mask : ThreeGranularityMask)
    (left right : ThreeEvidence) : Prop :=
  match left, right with
  | ThreeEvidence.favorable, ThreeEvidence.favorable => True
  | ThreeEvidence.corroborating, ThreeEvidence.corroborating => True
  | ThreeEvidence.unfavorable, ThreeEvidence.unfavorable => True
  | ThreeEvidence.favorable, ThreeEvidence.corroborating =>
      mask.favorableToCorroborating = true
  | ThreeEvidence.favorable, ThreeEvidence.unfavorable =>
      mask.favorableToUnfavorable = true
  | ThreeEvidence.corroborating, ThreeEvidence.favorable =>
      mask.corroboratingToFavorable = true
  | ThreeEvidence.corroborating, ThreeEvidence.unfavorable =>
      mask.corroboratingToUnfavorable = true
  | ThreeEvidence.unfavorable, ThreeEvidence.favorable =>
      mask.unfavorableToFavorable = true
  | ThreeEvidence.unfavorable, ThreeEvidence.corroborating =>
      mask.unfavorableToCorroborating = true

theorem ThreeGranularityMask.reflexive
    (mask : ThreeGranularityMask)
    (item : ThreeEvidence) :
    mask.relation item item := by
  cases item <;> exact True.intro

def ThreeGranularityMask.space
    (mask : ThreeGranularityMask) : RoughEvidenceSpace :=
  roughSpaceOf mask.relation threeEvidenceSupports
    (ThreeGranularityMask.reflexive mask)

def ThreeGranularityMask.Refines
    (fine coarse : ThreeGranularityMask) : Prop :=
  forall left right : ThreeEvidence,
    fine.relation left right -> coarse.relation left right

theorem mask_lower_preserved_under_refinement
    (coarse fine : ThreeGranularityMask)
    (hRefines : ThreeGranularityMask.Refines fine coarse)
    (item : ThreeEvidence)
    (hLower : LowerApprox coarse.space item) :
    LowerApprox fine.space item :=
  lower_preserved_under_relation_refinement
    threeEvidenceSupports
    coarse.relation
    fine.relation
    (ThreeGranularityMask.reflexive coarse)
    (ThreeGranularityMask.reflexive fine)
    hRefines
    item
    hLower

def allTrueThreeGranularityMask : ThreeGranularityMask :=
  { favorableToCorroborating := true
    favorableToUnfavorable := true
    corroboratingToFavorable := true
    corroboratingToUnfavorable := true
    unfavorableToFavorable := true
    unfavorableToCorroborating := true }

def identityThreeGranularityMask : ThreeGranularityMask :=
  { favorableToCorroborating := false
    favorableToUnfavorable := false
    corroboratingToFavorable := false
    corroboratingToUnfavorable := false
    unfavorableToFavorable := false
    unfavorableToCorroborating := false }

def allThreeGranularityMasks : List ThreeGranularityMask :=
  [false, true].flatMap (fun a =>
    [false, true].flatMap (fun b =>
      [false, true].flatMap (fun c =>
        [false, true].flatMap (fun d =>
          [false, true].flatMap (fun e =>
            [false, true].map (fun f =>
              { favorableToCorroborating := a
                favorableToUnfavorable := b
                corroboratingToFavorable := c
                corroboratingToUnfavorable := d
                unfavorableToFavorable := e
                unfavorableToCorroborating := f }))))))

theorem allThreeGranularityMasks_length :
    allThreeGranularityMasks.length = 64 := by
  native_decide

theorem identityThreeGranularityMask_refines_all_true :
    ThreeGranularityMask.Refines identityThreeGranularityMask
      allTrueThreeGranularityMask := by
  intro left right h
  cases left <;> cases right <;>
    repeat first
      | exact True.intro
      | exact rfl

theorem all_true_mask_favorable_not_lower :
    Not (LowerApprox allTrueThreeGranularityMask.space
      ThreeEvidence.favorable) := by
  intro hLower
  exact hLower.right ThreeEvidence.unfavorable rfl

theorem identity_mask_favorable_lower :
    LowerApprox identityThreeGranularityMask.space
      ThreeEvidence.favorable := by
  constructor
  case left =>
    exact True.intro
  case right =>
    intro other hRelated
    cases other
    case favorable =>
      exact True.intro
    case corroborating =>
      contradiction
    case unfavorable =>
      contradiction

theorem mask_payload_converse_failure :
    And
      (LowerApprox identityThreeGranularityMask.space
        ThreeEvidence.favorable)
      (Not (LowerApprox allTrueThreeGranularityMask.space
        ThreeEvidence.favorable)) :=
  And.intro identity_mask_favorable_lower
    all_true_mask_favorable_not_lower

def fineAdequacyModel : SigmaModel :=
  UnitPredicateModel (fun predicate => predicate = PredicateSymbol.adequate)

def fineAdequacyProfile :
    AdequacyProfile fineAdequacyModel :=
  { domain := AdequacyDomain.empirical
    evidence := Unit.unit
    context := Unit.unit
    claim := Unit.unit
    relevant := True
    sufficient := LowerApprox fineTwoEvidenceSpace TwoEvidence.favorable
    current := True
    methodologicallyFit := True
    uncertaintyBounded := True
    scopeMatched := True
    warrant := fun _ _ _ _ _ _ => rfl }

def fineAdequacyLink :
    RoughAdequacyLink fineAdequacyModel :=
  { space := fineTwoEvidenceSpace
    item := TwoEvidence.favorable
    profile := fineAdequacyProfile
    sufficientIffLower := Iff.rfl }

theorem fineAdequacyProfile_satisfied :
    AdequacyProfileSatisfied fineAdequacyProfile :=
  And.intro True.intro
    (And.intro fineTwoEvidence_favorable_lower
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro True.intro))))

theorem fineAdequacyProfile_to_adequate :
    fineAdequacyModel.interpPredicate PredicateSymbol.adequate
      (Args.cons fineAdequacyProfile.evidence
        (Args.cons fineAdequacyProfile.context
          (Args.cons fineAdequacyProfile.claim Args.nil))) :=
  AdequacyProfile_to_AdequateSem fineAdequacyProfile
    fineAdequacyProfile_satisfied

end Paralogic
