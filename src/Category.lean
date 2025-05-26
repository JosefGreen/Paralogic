import Mathlib.CategoryTheory.Basic
import Mathlib.Data.Nat.Cast
import Paralogic.Frames
import Paralogic.Stuckness

/-!
  src/Paralogic/Category.lean

  Categorical structure on Paralogic objects (frames + constraints),
  with insightScore‐monotone morphisms and composition.
-/


namespace Paralogic.Category

open CategoryTheory InnerProductSpace Paralogic.Frames Paralogic.Stuckness

/--
A Paralogic object bundles:
• A real inner-product space `E`.
• A Huber threshold `δ > 0`.
• A list of constraints `cs` on `E`.
-/
structure ParalogicObj where
  E        : Type*
  [normedAddCommGroup : NormedAddCommGroup E]
  [inner : InnerProductSpace ℝ E]
  δ        : ℝ
  hδ       : 0 < δ
  cs       : List Constraint

attribute [instance] ParalogicObj.normedAddCommGroup ParalogicObj.inner

/--
A Paralogic morphism `f : X ⟶ Y` is a continuous linear map `E_X → E_Y`
that does not increase the insightScore:
`insightScore X.cs v ≥ insightScore Y.cs (f v)`.
-/
structure ParalogicHom (X Y : ParalogicObj) where
  toFun           : X.E → Y.E
  continuous_linear : ContinuousLinearMap ℝ X.E Y.E
  insight_le      : ∀ v, insightScore X.hδ X.cs v ≥ insightScore Y.hδ Y.cs (toFun v)

infix:25 " ⟶ " => ParalogicHom

/-- Identity morphism: `id : X ⟶ X`. -/
def id (X : ParalogicObj) : X ⟶ X where
  toFun := id
  continuous_linear := ContinuousLinearMap.id ℝ X.E
  insight_le := fun v => by simp

/-- Composition of Paralogic morphisms. -/
def comp {X Y Z : ParalogicObj} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z where
  toFun := g.toFun ∘ f.toFun
  continuous_linear := g.continuous_linear.comp f.continuous_linear
  insight_le := fun v => (f.insight_le v).trans (g.insight_le (f.toFun v))

instance : Category ParalogicObj where
  Hom := ParalogicHom
  id := id
  comp := fun _ _ _ => comp

end Paralogic.Category
