import Paralogic.FoundationLemmas

/-!
Proof theory for the many-sorted formula layer.

This module starts Lane B of the whole-system completion pipeline.  The
calculus is intentionally modest: it covers premise use, truth introduction,
falsity elimination, conjunction, disjunction introduction/elimination,
implication introduction/elimination, and scoped current-value quantifier
rules.  The main result is a semantic soundness theorem against
`SatisfiesFormula`.

This is not a completeness theorem and it is not a full natural-deduction
system for quantified formulas.
-/

namespace Paralogic

def PremisesStableUnderUpdate
    (target : SortTag) (idx : Nat) (premises : List Formula) : Prop :=
  forall {M : SigmaModel} (rho : Assignment M)
    (value : M.Carrier target),
    SatisfiesAll rho premises ->
      SatisfiesAll (updateAssignment rho target idx value) premises

def PremisesStableUnderAllUpdates (premises : List Formula) : Prop :=
  forall (target : SortTag) (idx : Nat),
    PremisesStableUnderUpdate target idx premises

def PremisesQuantifierFreeFreshForUpdate
    (target : SortTag) (idx : Nat) (premises : List Formula) : Prop :=
  forall formula : Formula, List.Mem formula premises ->
    And (QuantifierFree formula) (Not (FormulaHasFreeVar target idx formula))

def PremisesFreshForUpdate
    (target : SortTag) (idx : Nat) (premises : List Formula) : Prop :=
  forall formula : Formula, List.Mem formula premises ->
    Not (FormulaHasFreeVar target idx formula)

theorem premises_stable_nil (target : SortTag) (idx : Nat) :
    PremisesStableUnderUpdate target idx [] := by
  intro _ _ _ _
  exact True.intro

theorem premises_stable_cons {target : SortTag} {idx : Nat}
    {formula : Formula} {rest : List Formula}
    (hFormula :
      forall {M : SigmaModel} (rho : Assignment M)
        (value : M.Carrier target),
        SatisfiesFormula rho formula ->
          SatisfiesFormula (updateAssignment rho target idx value) formula)
    (hRest : PremisesStableUnderUpdate target idx rest) :
    PremisesStableUnderUpdate target idx (formula :: rest) := by
  intro M rho value hAll
  exact And.intro
    (hFormula rho value hAll.left)
    (hRest rho value hAll.right)

theorem premises_stable_append {target : SortTag} {idx : Nat}
    {left right : List Formula}
    (hLeft : PremisesStableUnderUpdate target idx left)
    (hRight : PremisesStableUnderUpdate target idx right) :
    PremisesStableUnderUpdate target idx (left ++ right) := by
  intro M rho value hAll
  exact satisfies_all_append_intro
    (hLeft rho value (satisfies_all_append_left hAll))
    (hRight rho value (satisfies_all_append_right hAll))

theorem premises_stable_of_quantifier_free_fresh
    (target : SortTag) (idx : Nat) :
    (premises : List Formula) ->
      PremisesQuantifierFreeFreshForUpdate target idx premises ->
        PremisesStableUnderUpdate target idx premises
  | [], _ => premises_stable_nil target idx
  | formula :: rest, hFresh =>
      premises_stable_cons
        (fun rho value hSat =>
          (quantifier_free_satisfaction_stable_update_of_not_free rho target
            idx value formula
            (hFresh formula (List.Mem.head rest)).left
            (hFresh formula (List.Mem.head rest)).right).mp hSat)
        (premises_stable_of_quantifier_free_fresh target idx rest
          (fun restFormula hMem =>
            hFresh restFormula (List.Mem.tail formula hMem)))

theorem premises_stable_of_fresh
    (target : SortTag) (idx : Nat) :
    (premises : List Formula) ->
      PremisesFreshForUpdate target idx premises ->
        PremisesStableUnderUpdate target idx premises
  | [], _ => premises_stable_nil target idx
  | formula :: rest, hFresh =>
      premises_stable_cons
        (fun rho value hSat =>
          (satisfaction_stable_update_of_not_free rho target idx value
            formula (hFresh formula (List.Mem.head rest))).mp hSat)
        (premises_stable_of_fresh target idx rest
          (fun restFormula hMem =>
            hFresh restFormula (List.Mem.tail formula hMem)))

inductive Derives : List Formula -> Formula -> Prop where
  | premise {premises : List Formula} {formula : Formula} :
      List.Mem formula premises -> Derives premises formula
  | truth {premises : List Formula} :
      Derives premises Formula.truth
  | falsityElim {premises : List Formula} {formula : Formula} :
      Derives premises Formula.falsity ->
      Derives premises formula
  | conjIntro {premises : List Formula} {left right : Formula} :
      Derives premises left ->
      Derives premises right ->
      Derives premises (Formula.conj left right)
  | conjElimLeft {premises : List Formula} {left right : Formula} :
      Derives premises (Formula.conj left right) ->
      Derives premises left
  | conjElimRight {premises : List Formula} {left right : Formula} :
      Derives premises (Formula.conj left right) ->
      Derives premises right
  | disjIntroLeft {premises : List Formula} {left right : Formula} :
      Derives premises left ->
      Derives premises (Formula.disj left right)
  | disjIntroRight {premises : List Formula} {left right : Formula} :
      Derives premises right ->
      Derives premises (Formula.disj left right)
  | disjElim {premises : List Formula}
      {left right conclusion : Formula} :
      Derives premises (Formula.disj left right) ->
      Derives (left :: premises) conclusion ->
      Derives (right :: premises) conclusion ->
      Derives premises conclusion
  | implIntro {premises : List Formula} {left right : Formula} :
      Derives (left :: premises) right ->
      Derives premises (Formula.impl left right)
  | implElim {premises : List Formula} {left right : Formula} :
      Derives premises (Formula.impl left right) ->
      Derives premises left ->
      Derives premises right
  | forallCurrentElim {premises : List Formula}
      {s : SortTag} {idx : Nat} {body : Formula} :
      Derives premises (Formula.forallVar s idx body) ->
      Derives premises body
  | existsCurrentIntro {premises : List Formula}
      {s : SortTag} {idx : Nat} {body : Formula} :
      Derives premises body ->
      Derives premises (Formula.existsVar s idx body)
  | forallIntro {premises : List Formula}
      {s : SortTag} {idx : Nat} {body : Formula} :
      PremisesStableUnderUpdate s idx premises ->
      Derives premises body ->
      Derives premises (Formula.forallVar s idx body)

theorem satisfies_all_mem {M : SigmaModel} {rho : Assignment M}
    {premises : List Formula} {formula : Formula}
    (hAll : SatisfiesAll rho premises)
    (hMem : List.Mem formula premises) :
    SatisfiesFormula rho formula := by
  induction premises with
  | nil =>
      cases hMem
  | cons head tail ih =>
      cases hMem with
      | head =>
          exact hAll.left
      | tail _ hTail =>
          exact ih hAll.right hTail

theorem semantically_entails_forall_current
    (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [Formula.forallVar s idx body] body := by
  intro M rho hAll
  have hbody :
      SatisfiesFormula (updateAssignment rho s idx (rho s idx)) body :=
    hAll.left (rho s idx)
  rw [updateAssignment_current rho s idx] at hbody
  exact hbody

theorem semantically_entails_exists_current
    (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [body] (Formula.existsVar s idx body) := by
  intro M rho hAll
  refine Exists.intro (rho s idx) ?_
  rw [updateAssignment_current rho s idx]
  exact hAll.left

theorem semantically_entails_forall_intro_of_stable
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hStable : PremisesStableUnderUpdate s idx premises)
    (hEntails : SemanticallyEntails premises body) :
    SemanticallyEntails premises (Formula.forallVar s idx body) := by
  intro M rho hAll value
  exact hEntails M (updateAssignment rho s idx value)
    (hStable rho value hAll)

theorem semantically_entails_forall_intro_of_quantifier_free_fresh
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesQuantifierFreeFreshForUpdate s idx premises)
    (hEntails : SemanticallyEntails premises body) :
    SemanticallyEntails premises (Formula.forallVar s idx body) :=
  semantically_entails_forall_intro_of_stable
    (premises_stable_of_quantifier_free_fresh s idx premises hFresh)
    hEntails

theorem semantically_entails_forall_intro_of_fresh
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesFreshForUpdate s idx premises)
    (hEntails : SemanticallyEntails premises body) :
    SemanticallyEntails premises (Formula.forallVar s idx body) :=
  semantically_entails_forall_intro_of_stable
    (premises_stable_of_fresh s idx premises hFresh)
    hEntails

theorem derives_sound {premises : List Formula} {conclusion : Formula}
    (h : Derives premises conclusion) :
    SemanticallyEntails premises conclusion := by
  induction h with
  | premise hMem =>
      intro _ rho hAll
      exact satisfies_all_mem hAll hMem
  | truth =>
      intro _ _ _
      exact True.intro
  | falsityElim _ ih =>
      intro M rho hAll
      exact False.elim (ih M rho hAll)
  | conjIntro _ _ ihLeft ihRight =>
      intro M rho hAll
      exact And.intro (ihLeft M rho hAll) (ihRight M rho hAll)
  | conjElimLeft _ ih =>
      intro M rho hAll
      exact (ih M rho hAll).left
  | conjElimRight _ ih =>
      intro M rho hAll
      exact (ih M rho hAll).right
  | disjIntroLeft _ ih =>
      intro M rho hAll
      exact Or.inl (ih M rho hAll)
  | disjIntroRight _ ih =>
      intro M rho hAll
      exact Or.inr (ih M rho hAll)
  | disjElim _ _ _ ihDisj ihLeft ihRight =>
      intro M rho hAll
      exact Or.elim (ihDisj M rho hAll)
        (fun hleft => ihLeft M rho (And.intro hleft hAll))
        (fun hright => ihRight M rho (And.intro hright hAll))
  | implIntro _ ih =>
      intro M rho hAll hleft
      exact ih M rho (And.intro hleft hAll)
  | implElim _ _ ihImpl ihLeft =>
      intro M rho hAll
      exact (ihImpl M rho hAll) (ihLeft M rho hAll)
  | forallCurrentElim _ ih =>
      intro M rho hAll
      exact semantically_entails_forall_current _ _ _ M rho
        (And.intro (ih M rho hAll) True.intro)
  | existsCurrentIntro _ ih =>
      intro M rho hAll
      exact semantically_entails_exists_current _ _ _ M rho
        (And.intro (ih M rho hAll) True.intro)
  | forallIntro hStable _ ih =>
      intro M rho hAll value
      exact ih M (updateAssignment rho _ _ value)
        (hStable rho value hAll)

theorem semantic_countermodel_blocks_entailment
    {premises : List Formula} {conclusion : Formula}
    (countermodel : SemanticCountermodel premises conclusion) :
    Not (SemanticallyEntails premises conclusion) := by
  intro hEntails
  exact countermodel.conclusionFalse
    (hEntails countermodel.M countermodel.rho countermodel.premisesTrue)

theorem not_entails_has_countermodel
    {premises : List Formula} {conclusion : Formula}
    (h : Not (SemanticallyEntails premises conclusion)) :
    Nonempty (SemanticCountermodel premises conclusion) := by
  classical
  apply Classical.byContradiction
  intro hNoCountermodel
  apply h
  intro M rho hAll
  apply Classical.byContradiction
  intro hConclusionFalse
  apply hNoCountermodel
  exact Nonempty.intro
    { M := M
      rho := rho
      premisesTrue := hAll
      conclusionFalse := hConclusionFalse }

theorem derives_no_countermodel
    {premises : List Formula} {conclusion : Formula}
    (h : Derives premises conclusion) :
    Not (Nonempty (SemanticCountermodel premises conclusion)) := by
  intro hCountermodel
  cases hCountermodel with
  | intro countermodel =>
      exact semantic_countermodel_blocks_entailment countermodel
        (derives_sound h)

theorem derives_append_monotone_right
    {premises extra : List Formula} {conclusion : Formula}
    (hExtraStable : PremisesStableUnderAllUpdates extra)
    (h : Derives premises conclusion) :
    Derives (premises ++ extra) conclusion := by
  induction h with
  | premise hMem =>
      exact Derives.premise (List.mem_append_left extra hMem)
  | truth =>
      exact Derives.truth
  | falsityElim _ ih =>
      exact Derives.falsityElim ih
  | conjIntro _ _ ihLeft ihRight =>
      exact Derives.conjIntro ihLeft ihRight
  | conjElimLeft _ ih =>
      exact Derives.conjElimLeft ih
  | conjElimRight _ ih =>
      exact Derives.conjElimRight ih
  | disjIntroLeft _ ih =>
      exact Derives.disjIntroLeft ih
  | disjIntroRight _ ih =>
      exact Derives.disjIntroRight ih
  | disjElim _ _ _ ihDisj ihLeft ihRight =>
      exact Derives.disjElim ihDisj ihLeft ihRight
  | implIntro _ ih =>
      exact Derives.implIntro ih
  | implElim _ _ ihImpl ihLeft =>
      exact Derives.implElim ihImpl ihLeft
  | forallCurrentElim _ ih =>
      exact Derives.forallCurrentElim ih
  | existsCurrentIntro _ ih =>
      exact Derives.existsCurrentIntro ih
  | forallIntro hStable _ ih =>
      exact Derives.forallIntro
        (premises_stable_append hStable (hExtraStable _ _))
        ih

theorem derives_append_monotone_right_sound
    {premises extra : List Formula} {conclusion : Formula}
    (h : Derives premises conclusion) :
    SemanticallyEntails (premises ++ extra) conclusion :=
  semantically_entails_append_monotone_right (derives_sound h)

theorem derives_conj_left_example (left right : Formula) :
    Derives [Formula.conj left right] left :=
  Derives.conjElimLeft (Derives.premise (List.Mem.head []))

theorem derives_conj_left_example_sound (left right : Formula) :
    SemanticallyEntails [Formula.conj left right] left :=
  derives_sound (derives_conj_left_example left right)

theorem derives_modus_ponens_example (left right : Formula) :
    Derives [Formula.impl left right, left] right :=
  Derives.implElim
    (Derives.premise (List.Mem.head [left]))
    (Derives.premise (List.Mem.tail (Formula.impl left right)
      (List.Mem.head [])))

theorem derives_modus_ponens_example_sound (left right : Formula) :
    SemanticallyEntails [Formula.impl left right, left] right :=
  derives_sound (derives_modus_ponens_example left right)

theorem derives_implication_intro_example (left right : Formula) :
    Derives [right] (Formula.impl left right) :=
  Derives.implIntro
    (Derives.premise
      (List.Mem.tail left (List.Mem.head [])))

theorem derives_implication_intro_example_sound
    (left right : Formula) :
    SemanticallyEntails [right] (Formula.impl left right) :=
  derives_sound (derives_implication_intro_example left right)

theorem derives_falsity_elim_example (formula : Formula) :
    Derives [Formula.falsity] formula :=
  Derives.falsityElim
    (Derives.premise (List.Mem.head []))

theorem derives_falsity_elim_example_sound (formula : Formula) :
    SemanticallyEntails [Formula.falsity] formula :=
  derives_sound (derives_falsity_elim_example formula)

theorem derives_disj_elim_example
    (left right conclusion : Formula) :
    Derives
      [Formula.disj left right,
        Formula.impl left conclusion,
        Formula.impl right conclusion]
      conclusion :=
  Derives.disjElim
    (Derives.premise (List.Mem.head _))
    (Derives.implElim
      (Derives.premise
        (List.Mem.tail left
          (List.Mem.tail (Formula.disj left right)
            (List.Mem.head [Formula.impl right conclusion]))))
      (Derives.premise (List.Mem.head _)))
    (Derives.implElim
      (Derives.premise
        (List.Mem.tail right
          (List.Mem.tail (Formula.disj left right)
            (List.Mem.tail (Formula.impl left conclusion)
              (List.Mem.head [])))))
      (Derives.premise (List.Mem.head _)))

theorem derives_disj_elim_example_sound
    (left right conclusion : Formula) :
    SemanticallyEntails
      [Formula.disj left right,
        Formula.impl left conclusion,
        Formula.impl right conclusion]
      conclusion :=
  derives_sound (derives_disj_elim_example left right conclusion)

theorem derives_forall_current_example
    (s : SortTag) (idx : Nat) (body : Formula) :
    Derives [Formula.forallVar s idx body] body :=
  Derives.forallCurrentElim
    (Derives.premise (List.Mem.head []))

theorem derives_forall_current_example_sound
    (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [Formula.forallVar s idx body] body :=
  derives_sound (derives_forall_current_example s idx body)

theorem derives_exists_current_example
    (s : SortTag) (idx : Nat) (body : Formula) :
    Derives [body] (Formula.existsVar s idx body) :=
  Derives.existsCurrentIntro
    (Derives.premise (List.Mem.head []))

theorem derives_exists_current_example_sound
    (s : SortTag) (idx : Nat) (body : Formula) :
    SemanticallyEntails [body] (Formula.existsVar s idx body) :=
  derives_sound (derives_exists_current_example s idx body)

theorem derives_forall_truth_example
    (s : SortTag) (idx : Nat) :
    Derives [] (Formula.forallVar s idx Formula.truth) :=
  Derives.forallIntro (premises_stable_nil s idx) Derives.truth

theorem derives_forall_intro_of_quantifier_free_fresh
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesQuantifierFreeFreshForUpdate s idx premises)
    (hDerives : Derives premises body) :
    Derives premises (Formula.forallVar s idx body) :=
  Derives.forallIntro
    (premises_stable_of_quantifier_free_fresh s idx premises hFresh)
    hDerives

theorem derives_forall_intro_of_fresh
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesFreshForUpdate s idx premises)
    (hDerives : Derives premises body) :
    Derives premises (Formula.forallVar s idx body) :=
  Derives.forallIntro
    (premises_stable_of_fresh s idx premises hFresh)
    hDerives

theorem derives_forall_truth_example_sound
    (s : SortTag) (idx : Nat) :
    SemanticallyEntails [] (Formula.forallVar s idx Formula.truth) :=
  derives_sound (derives_forall_truth_example s idx)

theorem derives_forall_intro_of_quantifier_free_fresh_sound
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesQuantifierFreeFreshForUpdate s idx premises)
    (hDerives : Derives premises body) :
    SemanticallyEntails premises (Formula.forallVar s idx body) :=
  derives_sound
    (derives_forall_intro_of_quantifier_free_fresh hFresh hDerives)

theorem derives_forall_intro_of_fresh_sound
    {premises : List Formula} {s : SortTag} {idx : Nat} {body : Formula}
    (hFresh : PremisesFreshForUpdate s idx premises)
    (hDerives : Derives premises body) :
    SemanticallyEntails premises (Formula.forallVar s idx body) :=
  derives_sound (derives_forall_intro_of_fresh hFresh hDerives)

end Paralogic
