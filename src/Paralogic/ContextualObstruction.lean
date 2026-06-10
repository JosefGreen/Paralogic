/-!
Contextual obstruction layer.

This module is an exploratory mathematical spine for a more novel Paralogic:
local frame readings may be individually available while failing to extend to a
single global reading. This is inspired by sheaf-theoretic contextuality, but
kept deliberately abstract so it can later be specialized to institutional
frames, evidence contexts, evaluator views, or repair stages.
-/

namespace Paralogic

structure CoveredPresheaf : Type 1 where
  Ctx : Type
  le : Ctx -> Ctx -> Prop
  Sec : Ctx -> Type
  restrict :
    {small large : Ctx} -> le small large -> Sec large -> Sec small
  root : Ctx
  covered : Ctx -> Prop
  coverLe : (ctx : Ctx) -> covered ctx -> le ctx root

structure LocalFamily (P : CoveredPresheaf) : Type where
  localSection : (ctx : P.Ctx) -> P.covered ctx -> P.Sec ctx

def ExtendsRoot {P : CoveredPresheaf}
    (global : P.Sec P.root)
    (family : LocalFamily P) : Prop :=
  forall (ctx : P.Ctx) (hCovered : P.covered ctx),
    P.restrict (P.coverLe ctx hCovered) global =
      family.localSection ctx hCovered

def HasGlobalExtension {P : CoveredPresheaf}
    (family : LocalFamily P) : Prop :=
  Exists (fun global : P.Sec P.root => ExtendsRoot global family)

def ContextualObstruction {P : CoveredPresheaf}
    (family : LocalFamily P) : Prop :=
  Not (HasGlobalExtension family)

theorem global_extension_not_obstructed {P : CoveredPresheaf}
    {family : LocalFamily P}
    (h : HasGlobalExtension family) :
    Not (ContextualObstruction family) := by
  intro hObs
  exact hObs h

theorem obstruction_blocks_extension {P : CoveredPresheaf}
    {family : LocalFamily P}
    (hObs : ContextualObstruction family) :
    Not (HasGlobalExtension family) :=
  hObs

def CoverJointlyMonic (P : CoveredPresheaf) : Prop :=
  forall globalA globalB : P.Sec P.root,
    (forall (ctx : P.Ctx) (hCovered : P.covered ctx),
      P.restrict (P.coverLe ctx hCovered) globalA =
        P.restrict (P.coverLe ctx hCovered) globalB) ->
      globalA = globalB

theorem jointly_monic_global_extension_unique {P : CoveredPresheaf}
    (hJoint : CoverJointlyMonic P)
    {family : LocalFamily P}
    {globalA globalB : P.Sec P.root}
    (hA : ExtendsRoot globalA family)
    (hB : ExtendsRoot globalB family) :
    globalA = globalB := by
  apply hJoint
  intro ctx hCovered
  rw [hA ctx hCovered, hB ctx hCovered]

inductive TwoContext where
  | root
  | left
  | right
  deriving DecidableEq, Repr

def twoContextLe : TwoContext -> TwoContext -> Prop
  | TwoContext.root, TwoContext.root => True
  | TwoContext.left, TwoContext.left => True
  | TwoContext.right, TwoContext.right => True
  | TwoContext.left, TwoContext.root => True
  | TwoContext.right, TwoContext.root => True
  | _, _ => False

def BoolPairSec : TwoContext -> Type
  | TwoContext.root => Prod Bool Bool
  | TwoContext.left => Bool
  | TwoContext.right => Bool

def boolPairRestrict :
    {small large : TwoContext} ->
      twoContextLe small large -> BoolPairSec large -> BoolPairSec small
  | TwoContext.root, TwoContext.root, _, value => value
  | TwoContext.root, TwoContext.left, h, _ => False.elim h
  | TwoContext.root, TwoContext.right, h, _ => False.elim h
  | TwoContext.left, TwoContext.root, _, value => value.fst
  | TwoContext.left, TwoContext.left, _, value => value
  | TwoContext.left, TwoContext.right, h, _ => False.elim h
  | TwoContext.right, TwoContext.root, _, value => value.snd
  | TwoContext.right, TwoContext.left, h, _ => False.elim h
  | TwoContext.right, TwoContext.right, _, value => value

def twoContextCovered (ctx : TwoContext) : Prop :=
  ctx = TwoContext.left \/ ctx = TwoContext.right

theorem root_not_twoContextCovered :
    Not (twoContextCovered TwoContext.root) := by
  intro h
  cases h with
  | inl hLeft => cases hLeft
  | inr hRight => cases hRight

def BoolPairPresheaf : CoveredPresheaf :=
  { Ctx := TwoContext
    le := twoContextLe
    Sec := BoolPairSec
    restrict := boolPairRestrict
    root := TwoContext.root
    covered := twoContextCovered
    coverLe := by
      intro ctx hCovered
      cases ctx
      case root =>
        exact False.elim (root_not_twoContextCovered hCovered)
      case left =>
        exact True.intro
      case right =>
        exact True.intro }

def boolPairFamily (leftVal rightVal : Bool) :
    LocalFamily BoolPairPresheaf :=
  { localSection := by
      intro ctx hCovered
      cases ctx
      case root =>
        exact False.elim (root_not_twoContextCovered hCovered)
      case left =>
        exact leftVal
      case right =>
        exact rightVal }

theorem boolPairFamily_has_global_extension (leftVal rightVal : Bool) :
    HasGlobalExtension (boolPairFamily leftVal rightVal) := by
  exact Exists.intro (leftVal, rightVal) (by
    intro ctx hCovered
    cases ctx
    case root =>
      exact False.elim (root_not_twoContextCovered hCovered)
    case left =>
      rfl
    case right =>
      rfl)

theorem BoolPairPresheaf_jointly_monic :
    CoverJointlyMonic BoolPairPresheaf := by
  intro globalA globalB h
  cases globalA with
  | mk leftA rightA =>
      cases globalB with
      | mk leftB rightB =>
          have hLeft :
              leftA = leftB := h TwoContext.left (Or.inl rfl)
          have hRight :
              rightA = rightB := h TwoContext.right (Or.inr rfl)
          simp [hLeft, hRight]

inductive NoGlobalCtx where
  | root
  | impossible
  deriving DecidableEq, Repr

def noGlobalLe : NoGlobalCtx -> NoGlobalCtx -> Prop
  | NoGlobalCtx.root, NoGlobalCtx.root => True
  | NoGlobalCtx.impossible, NoGlobalCtx.impossible => True
  | NoGlobalCtx.impossible, NoGlobalCtx.root => True
  | _, _ => False

def NoGlobalSec : NoGlobalCtx -> Type
  | NoGlobalCtx.root => Empty
  | NoGlobalCtx.impossible => Unit

def noGlobalRestrict :
    {small large : NoGlobalCtx} ->
      noGlobalLe small large -> NoGlobalSec large -> NoGlobalSec small
  | NoGlobalCtx.root, NoGlobalCtx.root, _, global => global
  | NoGlobalCtx.root, NoGlobalCtx.impossible, h, _ => False.elim h
  | NoGlobalCtx.impossible, NoGlobalCtx.root, _, global => Empty.elim global
  | NoGlobalCtx.impossible, NoGlobalCtx.impossible, _, _ => Unit.unit

def noGlobalCovered (ctx : NoGlobalCtx) : Prop :=
  ctx = NoGlobalCtx.impossible

theorem noGlobalRoot_not_covered :
    Not (noGlobalCovered NoGlobalCtx.root) := by
  intro h
  cases h

def NoGlobalPresheaf : CoveredPresheaf :=
  { Ctx := NoGlobalCtx
    le := noGlobalLe
    Sec := NoGlobalSec
    restrict := noGlobalRestrict
    root := NoGlobalCtx.root
    covered := noGlobalCovered
    coverLe := by
      intro ctx hCovered
      cases ctx
      case root =>
        exact False.elim (noGlobalRoot_not_covered hCovered)
      case impossible =>
        exact True.intro }

def noGlobalFamily : LocalFamily NoGlobalPresheaf :=
  { localSection := by
      intro ctx hCovered
      cases ctx
      case root =>
        exact False.elim (noGlobalRoot_not_covered hCovered)
      case impossible =>
        exact Unit.unit }

theorem noGlobalFamily_obstructed :
    ContextualObstruction noGlobalFamily := by
  intro hGlobal
  cases hGlobal with
  | intro global _ =>
      cases global

end Paralogic
