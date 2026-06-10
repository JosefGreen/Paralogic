import Paralogic.ModelSemantics

/-!
Frame, context, and model morphisms.

This module turns translation language into typed preservation obligations.
A morphism is not merely a comparison or analogy: it maps every sort and states
which structure is preserved.
-/

namespace Paralogic

structure SortMap (M N : SigmaModel) where
  map : (s : SortTag) -> M.Carrier s -> N.Carrier s

def SortMap.onArgs {M N : SigmaModel} (h : SortMap M N) :
    {signature : List SortTag} ->
      Args M.Carrier signature -> Args N.Carrier signature :=
  fun {_signature} args => Args.map (fun {s} x => h.map s x) args

structure FunctionPreservingMap (M N : SigmaModel) extends SortMap M N where
  preservesFunction :
    forall (f : FunctionSymbol)
      (args : Args M.Carrier ((functionArity f).domain)),
      map ((functionArity f).codomain) (M.interpFunction f args) =
        N.interpFunction f (Args.map (fun {s} x => map s x) args)

structure ModelHom (M N : SigmaModel) extends FunctionPreservingMap M N where
  preservesPredicate :
    forall (p : PredicateSymbol)
      (args : Args M.Carrier ((predicateArity p).domain)),
      M.interpPredicate p args ->
        N.interpPredicate p (Args.map (fun {s} x => map s x) args)

def ModelHom.onArgs {M N : SigmaModel} (h : ModelHom M N) :
    {signature : List SortTag} ->
      Args M.Carrier signature -> Args N.Carrier signature :=
  fun {_signature} args => Args.map (fun {s} x => h.map s x) args

def identityModelHom (M : SigmaModel) : ModelHom M M :=
  { map := fun _ x => x
    preservesFunction := by
      intro _ args
      rw [Args.map_id args]
    preservesPredicate := by
      intro _ args h
      rw [Args.map_id args]
      exact h }

def composeModelHom {M N P : SigmaModel}
    (g : ModelHom N P) (f : ModelHom M N) : ModelHom M P :=
  { map := fun s x => g.map s (f.map s x)
    preservesFunction := by
      intro symbol args
      calc
        g.map ((functionArity symbol).codomain)
            (f.map ((functionArity symbol).codomain)
              (M.interpFunction symbol args))
          = g.map ((functionArity symbol).codomain)
              (N.interpFunction symbol
                (Args.map (fun {s} x => f.map s x) args)) := by
                rw [f.preservesFunction symbol args]
        _ = P.interpFunction symbol
              (Args.map (fun {s} x => g.map s x)
                (Args.map (fun {s} x => f.map s x) args)) := by
                rw [g.preservesFunction symbol
                  (Args.map (fun {s} x => f.map s x) args)]
        _ = P.interpFunction symbol
              (Args.map (fun {s} x => g.map s (f.map s x)) args) := by
                rw [Args.map_comp (fun {s} x => f.map s x)
                  (fun {s} x => g.map s x) args]
    preservesPredicate := by
      intro predicate args h
      have hn :
          N.interpPredicate predicate
            (Args.map (fun {s} x => f.map s x) args) :=
        f.preservesPredicate predicate args h
      have hp :
          P.interpPredicate predicate
            (Args.map (fun {s} x => g.map s x)
              (Args.map (fun {s} x => f.map s x) args)) :=
        g.preservesPredicate predicate
          (Args.map (fun {s} x => f.map s x) args) hn
      rw [Args.map_comp (fun {s} x => f.map s x)
        (fun {s} x => g.map s x) args] at hp
      exact hp }

theorem composeModelHom_map {M N P : SigmaModel}
    (g : ModelHom N P) (f : ModelHom M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeModelHom g f).map s x = g.map s (f.map s x) :=
  rfl

theorem composeModelHom_identity_left_map {M N : SigmaModel}
    (f : ModelHom M N) (s : SortTag) (x : M.Carrier s) :
    (composeModelHom (identityModelHom N) f).map s x = f.map s x :=
  rfl

theorem composeModelHom_identity_right_map {M N : SigmaModel}
    (f : ModelHom M N) (s : SortTag) (x : M.Carrier s) :
    (composeModelHom f (identityModelHom M)).map s x = f.map s x :=
  rfl

theorem composeModelHom_assoc_map {M N P Q : SigmaModel}
    (h : ModelHom P Q) (g : ModelHom N P) (f : ModelHom M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeModelHom h (composeModelHom g f)).map s x =
      (composeModelHom (composeModelHom h g) f).map s x :=
  rfl

def ModelHom.mapAssignment {M N : SigmaModel} (h : ModelHom M N)
    (rho : Assignment M) : Assignment N :=
  fun s idx => h.map s (rho s idx)

mutual

theorem ModelHom_preserves_evalTerm {M N : SigmaModel}
    (h : ModelHom M N) (rho : Assignment M) :
    {s : SortTag} -> (term : Term s) ->
      h.map s (evalTerm rho term) =
        evalTerm (ModelHom.mapAssignment h rho) term
  | _, Term.var _ => rfl
  | _, Term.app symbol args => by
      rw [evalTerm, evalTerm]
      calc
        h.map ((functionArity symbol).codomain)
            (M.interpFunction symbol (evalArgs rho args))
          = N.interpFunction symbol
              (Args.map (fun {s} x => h.map s x) (evalArgs rho args)) := by
                exact h.preservesFunction symbol (evalArgs rho args)
        _ = N.interpFunction symbol
              (evalArgs (ModelHom.mapAssignment h rho) args) := by
                rw [ModelHom_preserves_evalArgs h rho args]

theorem ModelHom_preserves_evalArgs {M N : SigmaModel}
    (h : ModelHom M N) (rho : Assignment M) :
    {signature : List SortTag} -> (args : Args Term signature) ->
      Args.map (fun {s} x => h.map s x) (evalArgs rho args) =
        evalArgs (ModelHom.mapAssignment h rho) args
  | [], Args.nil => rfl
  | _ :: _, Args.cons term rest => by
      rw [evalArgs, evalArgs, Args.map,
        ModelHom_preserves_evalTerm h rho term,
        ModelHom_preserves_evalArgs h rho rest]

end

def PositiveQuantifierFreeFormula : Formula -> Prop
  | Formula.truth => True
  | Formula.falsity => True
  | Formula.atom _ _ => True
  | Formula.conj left right =>
      And (PositiveQuantifierFreeFormula left)
        (PositiveQuantifierFreeFormula right)
  | Formula.disj left right =>
      And (PositiveQuantifierFreeFormula left)
        (PositiveQuantifierFreeFormula right)
  | Formula.impl _ _ => False
  | Formula.neg _ => False
  | Formula.forallVar _ _ _ => False
  | Formula.existsVar _ _ _ => False

theorem ModelHom_preserves_positive_quantifier_free_satisfaction
    {M N : SigmaModel} (h : ModelHom M N) (rho : Assignment M) :
    (formula : Formula) ->
      PositiveQuantifierFreeFormula formula ->
        SatisfiesFormula rho formula ->
          SatisfiesFormula (ModelHom.mapAssignment h rho) formula
  | Formula.truth, _, _ => True.intro
  | Formula.falsity, _, hs => False.elim hs
  | Formula.atom p args, _, hs => by
      rw [SatisfiesFormula]
      rw [← ModelHom_preserves_evalArgs h rho args]
      exact h.preservesPredicate p (evalArgs rho args) hs
  | Formula.conj left right, hPositive, hs =>
      And.intro
        (ModelHom_preserves_positive_quantifier_free_satisfaction h rho
          left hPositive.left hs.left)
        (ModelHom_preserves_positive_quantifier_free_satisfaction h rho
          right hPositive.right hs.right)
  | Formula.disj left right, hPositive, hs =>
      Or.elim hs
        (fun hleft =>
          Or.inl
            (ModelHom_preserves_positive_quantifier_free_satisfaction h rho
              left hPositive.left hleft))
        (fun hright =>
          Or.inr
            (ModelHom_preserves_positive_quantifier_free_satisfaction h rho
              right hPositive.right hright))
  | Formula.impl _ _, hPositive, _ => False.elim hPositive
  | Formula.neg _, hPositive, _ => False.elim hPositive
  | Formula.forallVar _ _ _, hPositive, _ => False.elim hPositive
  | Formula.existsVar _ _ _, hPositive, _ => False.elim hPositive

theorem args_map_left_inverse {A B : SortTag -> Type}
    (forward : {s : SortTag} -> A s -> B s)
    (backward : {s : SortTag} -> B s -> A s)
    (hInv : forall (s : SortTag) (x : A s),
      backward (forward x) = x) :
    {signature : List SortTag} -> (args : Args A signature) ->
      Args.map backward (Args.map forward args) = args
  | [], Args.nil => rfl
  | _ :: _, Args.cons x xs => by
      rw [Args.map, Args.map, hInv _ x,
        args_map_left_inverse forward backward hInv xs]

structure ModelIso (M N : SigmaModel) where
  forward : ModelHom M N
  backward : ModelHom N M
  leftInverse :
    forall (s : SortTag) (x : M.Carrier s),
      backward.map s (forward.map s x) = x
  rightInverse :
    forall (s : SortTag) (y : N.Carrier s),
      forward.map s (backward.map s y) = y

def identityModelIso (M : SigmaModel) : ModelIso M M :=
  { forward := identityModelHom M
    backward := identityModelHom M
    leftInverse := by
      intro _ _
      rfl
    rightInverse := by
      intro _ _
      rfl }

def composeModelIso {M N P : SigmaModel}
    (second : ModelIso N P) (first : ModelIso M N) :
    ModelIso M P :=
  { forward := composeModelHom second.forward first.forward
    backward := composeModelHom first.backward second.backward
    leftInverse := by
      intro s x
      change first.backward.map s
          (second.backward.map s
            (second.forward.map s (first.forward.map s x))) = x
      rw [second.leftInverse s (first.forward.map s x),
        first.leftInverse s x]
    rightInverse := by
      intro s y
      change second.forward.map s
          (first.forward.map s
            (first.backward.map s (second.backward.map s y))) = y
      rw [first.rightInverse s (second.backward.map s y),
        second.rightInverse s y] }

theorem composeModelIso_forward_map {M N P : SigmaModel}
    (second : ModelIso N P) (first : ModelIso M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeModelIso second first).forward.map s x =
      second.forward.map s (first.forward.map s x) :=
  rfl

theorem ModelIso_reflectsPredicate {M N : SigmaModel}
    (iso : ModelIso M N)
    (predicate : PredicateSymbol)
    (args : Args M.Carrier ((predicateArity predicate).domain))
    (hTarget :
      N.interpPredicate predicate
        (Args.map (fun {s} x => iso.forward.map s x) args)) :
    M.interpPredicate predicate args := by
  have hBack :
      M.interpPredicate predicate
        (Args.map (fun {s} x => iso.backward.map s x)
          (Args.map (fun {s} x => iso.forward.map s x) args)) :=
    iso.backward.preservesPredicate predicate
      (Args.map (fun {s} x => iso.forward.map s x) args) hTarget
  rw [args_map_left_inverse
    (fun {s} x => iso.forward.map s x)
    (fun {s} x => iso.backward.map s x)
    iso.leftInverse args] at hBack
  exact hBack

theorem ModelIso_positive_quantifier_free_satisfaction_iff
    {M N : SigmaModel} (iso : ModelIso M N) (rho : Assignment M) :
    (formula : Formula) ->
      PositiveQuantifierFreeFormula formula ->
        Iff (SatisfiesFormula rho formula)
          (SatisfiesFormula
            (ModelHom.mapAssignment iso.forward rho) formula)
  | Formula.truth, _ =>
      Iff.intro (fun _ => True.intro) (fun _ => True.intro)
  | Formula.falsity, _ =>
      Iff.intro (fun h => h) (fun h => h)
  | Formula.atom p args, _ =>
      Iff.intro
        (fun hs =>
          ModelHom_preserves_positive_quantifier_free_satisfaction
            iso.forward rho (Formula.atom p args) True.intro hs)
        (fun hs => by
          rw [SatisfiesFormula] at hs
          rw [← ModelHom_preserves_evalArgs iso.forward rho args] at hs
          exact ModelIso_reflectsPredicate iso p (evalArgs rho args) hs)
  | Formula.conj left right, hPositive =>
      let hLeft :=
        ModelIso_positive_quantifier_free_satisfaction_iff iso rho
          left hPositive.left
      let hRight :=
        ModelIso_positive_quantifier_free_satisfaction_iff iso rho
          right hPositive.right
      Iff.intro
        (fun hs => And.intro (hLeft.mp hs.left) (hRight.mp hs.right))
        (fun hs => And.intro (hLeft.mpr hs.left) (hRight.mpr hs.right))
  | Formula.disj left right, hPositive =>
      let hLeft :=
        ModelIso_positive_quantifier_free_satisfaction_iff iso rho
          left hPositive.left
      let hRight :=
        ModelIso_positive_quantifier_free_satisfaction_iff iso rho
          right hPositive.right
      Iff.intro
        (fun hs =>
          Or.elim hs
            (fun hleft => Or.inl (hLeft.mp hleft))
            (fun hright => Or.inr (hRight.mp hright)))
        (fun hs =>
          Or.elim hs
            (fun hleft => Or.inl (hLeft.mpr hleft))
            (fun hright => Or.inr (hRight.mpr hright)))
  | Formula.impl _ _, hPositive => False.elim hPositive
  | Formula.neg _, hPositive => False.elim hPositive
  | Formula.forallVar _ _ _, hPositive => False.elim hPositive
  | Formula.existsVar _ _ _, hPositive => False.elim hPositive

theorem ModelIso_forward_updateAssignment {M N : SigmaModel}
    (iso : ModelIso M N) (rho : Assignment M)
    (target : SortTag) (idx : Nat)
    (value : N.Carrier target) :
    updateAssignment (ModelHom.mapAssignment iso.forward rho) target idx value =
      ModelHom.mapAssignment iso.forward
        (updateAssignment rho target idx (iso.backward.map target value)) := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [updateAssignment, ModelHom.mapAssignment, iso.rightInverse]
    · simp [updateAssignment, ModelHom.mapAssignment, hn]
  · simp [updateAssignment, ModelHom.mapAssignment, hs]

theorem ModelIso_forward_updateAssignment_source {M N : SigmaModel}
    (iso : ModelIso M N) (rho : Assignment M)
    (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    updateAssignment (ModelHom.mapAssignment iso.forward rho) target idx
        (iso.forward.map target value) =
      ModelHom.mapAssignment iso.forward
        (updateAssignment rho target idx value) := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [updateAssignment, ModelHom.mapAssignment]
    · simp [updateAssignment, ModelHom.mapAssignment, hn]
  · simp [updateAssignment, ModelHom.mapAssignment, hs]

theorem ModelIso_backward_updateAssignment {M N : SigmaModel}
    (iso : ModelIso M N) (rho : Assignment M)
    (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    updateAssignment rho target idx value =
      ModelHom.mapAssignment iso.backward
        (updateAssignment (ModelHom.mapAssignment iso.forward rho) target idx
          (iso.forward.map target value)) := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [updateAssignment, ModelHom.mapAssignment, iso.leftInverse]
    · simp [updateAssignment, ModelHom.mapAssignment, hn, iso.leftInverse]
  · simp [updateAssignment, ModelHom.mapAssignment, hs, iso.leftInverse]

theorem ModelIso_full_formula_satisfaction_iff
    {M N : SigmaModel} (iso : ModelIso M N) (rho : Assignment M) :
    (formula : Formula) ->
      Iff (SatisfiesFormula rho formula)
        (SatisfiesFormula (ModelHom.mapAssignment iso.forward rho) formula)
  | Formula.truth =>
      Iff.intro (fun _ => True.intro) (fun _ => True.intro)
  | Formula.falsity =>
      Iff.intro (fun h => h) (fun h => h)
  | Formula.atom p args =>
      Iff.intro
        (fun hs =>
          ModelHom_preserves_positive_quantifier_free_satisfaction
            iso.forward rho (Formula.atom p args) True.intro hs)
        (fun hs => by
          rw [SatisfiesFormula] at hs
          rw [← ModelHom_preserves_evalArgs iso.forward rho args] at hs
          exact ModelIso_reflectsPredicate iso p (evalArgs rho args) hs)
  | Formula.conj left right =>
      let hLeft := ModelIso_full_formula_satisfaction_iff iso rho left
      let hRight := ModelIso_full_formula_satisfaction_iff iso rho right
      Iff.intro
        (fun hs => And.intro (hLeft.mp hs.left) (hRight.mp hs.right))
        (fun hs => And.intro (hLeft.mpr hs.left) (hRight.mpr hs.right))
  | Formula.disj left right =>
      let hLeft := ModelIso_full_formula_satisfaction_iff iso rho left
      let hRight := ModelIso_full_formula_satisfaction_iff iso rho right
      Iff.intro
        (fun hs =>
          Or.elim hs
            (fun hleft => Or.inl (hLeft.mp hleft))
            (fun hright => Or.inr (hRight.mp hright)))
        (fun hs =>
          Or.elim hs
            (fun hleft => Or.inl (hLeft.mpr hleft))
            (fun hright => Or.inr (hRight.mpr hright)))
  | Formula.impl left right =>
      let hLeft := ModelIso_full_formula_satisfaction_iff iso rho left
      let hRight := ModelIso_full_formula_satisfaction_iff iso rho right
      Iff.intro
        (fun hs hTargetLeft =>
          hRight.mp (hs (hLeft.mpr hTargetLeft)))
        (fun hs hSourceLeft =>
          hRight.mpr (hs (hLeft.mp hSourceLeft)))
  | Formula.neg body =>
      let hBody := ModelIso_full_formula_satisfaction_iff iso rho body
      Iff.intro
        (fun hs hTarget => hs (hBody.mpr hTarget))
        (fun hs hSource => hs (hBody.mp hSource))
  | Formula.forallVar s idx body =>
      Iff.intro
        (fun hs value => by
          rw [ModelIso_forward_updateAssignment iso rho s idx value]
          exact (ModelIso_full_formula_satisfaction_iff iso
            (updateAssignment rho s idx (iso.backward.map s value)) body).mp
            (hs (iso.backward.map s value)))
        (fun hs value => by
          have hTarget := hs (iso.forward.map s value)
          rw [ModelIso_forward_updateAssignment_source iso rho s idx value]
            at hTarget
          have hBody :=
            (ModelIso_full_formula_satisfaction_iff iso
              (updateAssignment rho s idx value) body).mpr hTarget
          exact hBody)
  | Formula.existsVar s idx body =>
      Iff.intro
        (fun hs =>
          Exists.elim hs
            (fun value hBody =>
              Exists.intro (iso.forward.map s value) (by
                have hMapped :=
                  (ModelIso_full_formula_satisfaction_iff iso
                    (updateAssignment rho s idx value) body).mp hBody
                rw [← ModelIso_forward_updateAssignment_source iso rho s idx
                  value] at hMapped
                exact hMapped)))
        (fun hs =>
          Exists.elim hs
            (fun value hBody =>
              Exists.intro (iso.backward.map s value) (by
                rw [ModelIso_forward_updateAssignment iso rho s idx value]
                  at hBody
                exact (ModelIso_full_formula_satisfaction_iff iso
                  (updateAssignment rho s idx (iso.backward.map s value))
                  body).mpr hBody)))

structure FrameContextMorphism (M N : SigmaModel) extends ModelHom M N where
  preservesFrameContextContradiction :
    forall (frame : M.Carrier SortTag.frame)
      (ctx : M.Carrier SortTag.context)
      (claim : M.Carrier SortTag.claim),
      M.interpPredicate PredicateSymbol.contradictionPresent
        (Args.cons frame (Args.cons ctx (Args.cons claim Args.nil))) ->
      N.interpPredicate PredicateSymbol.contradictionPresent
        (Args.cons (map SortTag.frame frame)
          (Args.cons (map SortTag.context ctx)
            (Args.cons (map SortTag.claim claim) Args.nil)))
  preservesDirectionalFrameChange :
    forall (source target : M.Carrier SortTag.frame),
      DirectionalNonEquivalenceSem source target ->
      DirectionalNonEquivalenceSem (M := N) (map SortTag.frame source)
        (map SortTag.frame target)

def identityFrameContextMorphism (M : SigmaModel) :
    FrameContextMorphism M M :=
  { identityModelHom M with
    preservesFrameContextContradiction := by
      intro _ _ _ h
      exact h
    preservesDirectionalFrameChange := by
      intro _ _ h
      exact h }

def composeFrameContextMorphism {M N P : SigmaModel}
    (g : FrameContextMorphism N P)
    (f : FrameContextMorphism M N) : FrameContextMorphism M P :=
  { composeModelHom g.toModelHom f.toModelHom with
    preservesFrameContextContradiction := by
      intro frame ctx claim h
      exact g.preservesFrameContextContradiction
        (f.map SortTag.frame frame)
        (f.map SortTag.context ctx)
        (f.map SortTag.claim claim)
        (f.preservesFrameContextContradiction frame ctx claim h)
    preservesDirectionalFrameChange := by
      intro source target h
      exact g.preservesDirectionalFrameChange
        (f.map SortTag.frame source)
        (f.map SortTag.frame target)
        (f.preservesDirectionalFrameChange source target h) }

theorem composeFrameContextMorphism_map {M N P : SigmaModel}
    (g : FrameContextMorphism N P)
    (f : FrameContextMorphism M N)
    (s : SortTag) (x : M.Carrier s) :
    (composeFrameContextMorphism g f).map s x = g.map s (f.map s x) :=
  rfl

structure PreservationProfile where
  preservesUses : Prop
  preservesClaims : Prop
  preservesSupportDegraded : Prop
  preservesTreatment : Prop
  preservesPower : Prop
  preservesEvaluatorAcceptance : Prop
  preservesNormativeBridge : Prop
  preservesEmpiricalValidation : Prop

def totalPreservationProfile : PreservationProfile :=
  { preservesUses := True
    preservesClaims := True
    preservesSupportDegraded := True
    preservesTreatment := True
    preservesPower := True
    preservesEvaluatorAcceptance := True
    preservesNormativeBridge := True
    preservesEmpiricalValidation := True }

def minimalFrameProfile : PreservationProfile :=
  { preservesUses := False
    preservesClaims := False
    preservesSupportDegraded := False
    preservesTreatment := False
    preservesPower := False
    preservesEvaluatorAcceptance := False
    preservesNormativeBridge := False
    preservesEmpiricalValidation := False }

structure FormulaTranslation (M N : SigmaModel) where
  translateFormula : Formula -> Formula
  translateAssignment : Assignment M -> Assignment N
  preservesSatisfaction :
    forall (rho : Assignment M) (formula : Formula),
      SatisfiesFormula rho formula ->
        SatisfiesFormula (translateAssignment rho) (translateFormula formula)

theorem FormulaTranslation_apply {M N : SigmaModel}
    (translation : FormulaTranslation M N)
    (rho : Assignment M) (formula : Formula)
    (h : SatisfiesFormula rho formula) :
    SatisfiesFormula (translation.translateAssignment rho)
      (translation.translateFormula formula) :=
  translation.preservesSatisfaction rho formula h

def FormulaTranslation.translatePremises {M N : SigmaModel}
    (translation : FormulaTranslation M N) :
    List Formula -> List Formula :=
  List.map translation.translateFormula

theorem FormulaTranslation_preserves_satisfies_all {M N : SigmaModel}
    (translation : FormulaTranslation M N)
    (rho : Assignment M) :
    (premises : List Formula) ->
      SatisfiesAll rho premises ->
        SatisfiesAll (translation.translateAssignment rho)
          (translation.translatePremises premises)
  | [], _ => True.intro
  | formula :: rest, hAll =>
      And.intro
        (translation.preservesSatisfaction rho formula hAll.left)
        (FormulaTranslation_preserves_satisfies_all translation rho
          rest hAll.right)

theorem FormulaTranslation_transports_semantic_entailment_instance
    {M N : SigmaModel} (translation : FormulaTranslation M N)
    {premises : List Formula} {conclusion : Formula}
    (hEntails : SemanticallyEntails premises conclusion)
    (rho : Assignment M)
    (hAll : SatisfiesAll rho premises) :
    And
      (SatisfiesAll (translation.translateAssignment rho)
        (translation.translatePremises premises))
      (SatisfiesFormula (translation.translateAssignment rho)
        (translation.translateFormula conclusion)) :=
  And.intro
    (FormulaTranslation_preserves_satisfies_all translation rho premises hAll)
    (translation.preservesSatisfaction rho conclusion (hEntails M rho hAll))

def identityFormulaTranslation (M : SigmaModel) :
    FormulaTranslation M M :=
  { translateFormula := fun formula => formula
    translateAssignment := fun rho => rho
    preservesSatisfaction := by
      intro _ _ h
      exact h }

def composeFormulaTranslation {M N P : SigmaModel}
    (second : FormulaTranslation N P)
    (first : FormulaTranslation M N) :
    FormulaTranslation M P :=
  { translateFormula := fun formula =>
      second.translateFormula (first.translateFormula formula)
    translateAssignment := fun rho =>
      second.translateAssignment (first.translateAssignment rho)
    preservesSatisfaction := by
      intro rho formula h
      exact second.preservesSatisfaction
        (first.translateAssignment rho)
        (first.translateFormula formula)
        (first.preservesSatisfaction rho formula h) }

theorem composeFormulaTranslation_apply {M N P : SigmaModel}
    (second : FormulaTranslation N P)
    (first : FormulaTranslation M N)
    (formula : Formula) :
    (composeFormulaTranslation second first).translateFormula formula =
      second.translateFormula (first.translateFormula formula) :=
  rfl

theorem identityFormulaTranslation_apply (M : SigmaModel)
    (formula : Formula) :
    (identityFormulaTranslation M).translateFormula formula = formula :=
  rfl

structure ProjectionLaw (M N : SigmaModel) where
  profile : PreservationProfile
  translation : FormulaTranslation M N
  sourceFrame : M.Carrier SortTag.frame
  targetFrame : N.Carrier SortTag.frame
  sourceContext : M.Carrier SortTag.context
  targetContext : N.Carrier SortTag.context

structure BidirectionalTranslation (M N : SigmaModel) where
  forward : FormulaTranslation M N
  backward : FormulaTranslation N M
  roundTripForward :
    forall (rho : Assignment M) (formula : Formula),
      SatisfiesFormula rho formula ->
        SatisfiesFormula
          (backward.translateAssignment (forward.translateAssignment rho))
          (backward.translateFormula (forward.translateFormula formula))
  roundTripBackward :
    forall (rho : Assignment N) (formula : Formula),
      SatisfiesFormula rho formula ->
        SatisfiesFormula
          (forward.translateAssignment (backward.translateAssignment rho))
          (forward.translateFormula (backward.translateFormula formula))

theorem ModelHom_preserves_UsesSem {M N : SigmaModel} (h : ModelHom M N)
    {i : M.Carrier SortTag.institution}
    {o : M.Carrier SortTag.symbolicOutput}
    (hu : UsesSem i o) :
    UsesSem (M := N) (h.map SortTag.institution i)
      (h.map SortTag.symbolicOutput o) :=
  h.preservesPredicate PredicateSymbol.uses
    (Args.cons i (Args.cons o Args.nil)) hu

theorem ModelHom_preserves_ClaimsSem {M N : SigmaModel} (h : ModelHom M N)
    {i : M.Carrier SortTag.institution}
    {o : M.Carrier SortTag.symbolicOutput}
    {c : M.Carrier SortTag.claim}
    (hc : ClaimsSem i o c) :
    ClaimsSem (M := N) (h.map SortTag.institution i)
      (h.map SortTag.symbolicOutput o) (h.map SortTag.claim c) :=
  h.preservesPredicate PredicateSymbol.claims
    (Args.cons i (Args.cons o (Args.cons c Args.nil))) hc

theorem ModelHom_preserves_ISFSem {M N : SigmaModel} (h : ModelHom M N)
    {i : M.Carrier SortTag.institution}
    {o : M.Carrier SortTag.symbolicOutput}
    {c : M.Carrier SortTag.claim}
    {e : M.Carrier SortTag.evidenceSet}
    {ctx : M.Carrier SortTag.context}
    (hisf : ISFSem M i o c e ctx) :
    ISFSem N (h.map SortTag.institution i)
      (h.map SortTag.symbolicOutput o)
      (h.map SortTag.claim c)
      (h.map SortTag.evidenceSet e)
      (h.map SortTag.context ctx) :=
  { uses := ModelHom_preserves_UsesSem h hisf.uses
    claims := ModelHom_preserves_ClaimsSem h hisf.claims
    supportDegraded :=
      h.preservesPredicate PredicateSymbol.supportDegraded
        (Args.cons e (Args.cons ctx (Args.cons c Args.nil)))
        hisf.supportDegraded
    treatsAsAdequate :=
      h.preservesPredicate PredicateSymbol.treatsAsAdequate
        (Args.cons i (Args.cons o (Args.cons c (Args.cons ctx Args.nil))))
        hisf.treatsAsAdequate }

theorem ModelHom_preserves_EvaluatorAcceptsSem {M N : SigmaModel}
    (h : ModelHom M N)
    {ev : M.Carrier SortTag.evaluator}
    {x : M.Carrier SortTag.candidateInsight}
    (ha : EvaluatorAcceptsSem ev x) :
    EvaluatorAcceptsSem (M := N) (h.map SortTag.evaluator ev)
      (h.map SortTag.candidateInsight x) :=
  h.preservesPredicate PredicateSymbol.evaluatorAccepts
    (Args.cons ev (Args.cons x Args.nil)) ha

theorem ModelHom_preserves_ValidInsightSem {M N : SigmaModel}
    (h : ModelHom M N)
    {x : M.Carrier SortTag.candidateInsight}
    {ev : M.Carrier SortTag.evaluator}
    {source target : M.Carrier SortTag.frame}
    {c : M.Carrier SortTag.claim}
    (hv : ValidInsightSem M x ev source target c) :
    ValidInsightSem N (h.map SortTag.candidateInsight x)
      (h.map SortTag.evaluator ev)
      (h.map SortTag.frame source)
      (h.map SortTag.frame target)
      (h.map SortTag.claim c) :=
  { candidateInsight :=
      h.preservesPredicate PredicateSymbol.candidateInsight
        (Args.cons x Args.nil) hv.candidateInsight
    evaluatorAccepts := ModelHom_preserves_EvaluatorAcceptsSem h
      hv.evaluatorAccepts
    licensedTransition :=
      h.preservesPredicate PredicateSymbol.licensedTransition
        (Args.cons x (Args.cons source (Args.cons target Args.nil)))
        hv.licensedTransition
    nonTrivialTransformation :=
      h.preservesPredicate PredicateSymbol.nonTrivialTransformation
        (Args.cons x (Args.cons source (Args.cons target Args.nil)))
        hv.nonTrivialTransformation
    contradictionAddressed :=
      h.preservesPredicate PredicateSymbol.contradictionAddressed
        (Args.cons x (Args.cons c Args.nil)) hv.contradictionAddressed
    noHigherOrderDefeater :=
      h.preservesPredicate PredicateSymbol.noHigherOrderDefeater
        (Args.cons ev (Args.cons x Args.nil)) hv.noHigherOrderDefeater
    generativityMinimal :=
      h.preservesPredicate PredicateSymbol.generativityMinimal
        (Args.cons x Args.nil) hv.generativityMinimal
    directionalNonEquivalence :=
      h.preservesPredicate PredicateSymbol.directionalNonEquivalence
        (Args.cons source (Args.cons target Args.nil))
        hv.directionalNonEquivalence }

end Paralogic
