import Paralogic.ModelSemantics

/-!
Foundation lemmas for the many-sorted syntax and semantics layer.

These lemmas close the first part of Gate 1 in the completion pipeline:
identity substitution, satisfaction eliminators/constructors, and basic
semantic-entailment rules.
-/

namespace Paralogic

mutual

theorem substTerm_identity :
    {s : SortTag} -> (term : Term s) ->
      substTerm identitySubstitution term = term
  | _, Term.var _ => rfl
  | _, Term.app f args => by
      change Term.app f (substArgs identitySubstitution args) = Term.app f args
      rw [substArgs_identity args]

theorem substArgs_identity :
    {signature : List SortTag} -> (args : Args Term signature) ->
      substArgs identitySubstitution args = args
  | [], Args.nil => rfl
  | _ :: _, Args.cons x xs => by
      rw [substArgs, substTerm_identity x, substArgs_identity xs]

end

theorem maskSubstitution_identity (target : SortTag) (idx : Nat) :
    maskSubstitution target idx identitySubstitution = identitySubstitution := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [maskSubstitution, identitySubstitution]
    · simp [maskSubstitution, identitySubstitution, hn]
  · simp [maskSubstitution, identitySubstitution, hs]

theorem substFormula_identity (formula : Formula) :
    substFormula identitySubstitution formula = formula := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom p args =>
      rw [substFormula, substArgs_identity args]
  | conj left right ihLeft ihRight =>
      rw [substFormula, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      rw [substFormula, ihLeft, ihRight]
  | impl left right ihLeft ihRight =>
      rw [substFormula, ihLeft, ihRight]
  | neg body ih =>
      rw [substFormula, ih]
  | forallVar s idx body ih =>
      rw [substFormula, maskSubstitution_identity s idx, ih]
  | existsVar s idx body ih =>
      rw [substFormula, maskSubstitution_identity s idx, ih]

theorem quantified_variable_not_free_forall (s : SortTag) (idx : Nat)
    (body : Formula) :
    Not (FormulaHasFreeVar s idx (Formula.forallVar s idx body)) := by
  simp [FormulaHasFreeVar]

theorem quantified_variable_not_free_exists (s : SortTag) (idx : Nat)
    (body : Formula) :
    Not (FormulaHasFreeVar s idx (Formula.existsVar s idx body)) := by
  simp [FormulaHasFreeVar]

theorem updateAssignment_current {M : SigmaModel} (rho : Assignment M)
    (target : SortTag) (idx : Nat) :
    updateAssignment rho target idx (rho target idx) = rho := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [updateAssignment]
    · simp [updateAssignment, hn]
  · simp [updateAssignment, hs]

theorem updateAssignment_shadow_same {M : SigmaModel} (rho : Assignment M)
    (target : SortTag) (idx : Nat)
    (first second : M.Carrier target) :
    updateAssignment (updateAssignment rho target idx first) target idx
      second =
        updateAssignment rho target idx second := by
  funext s n
  by_cases hs : s = target
  · subst hs
    by_cases hn : n = idx
    · subst hn
      simp [updateAssignment]
    · simp [updateAssignment, hn]
  · simp [updateAssignment, hs]

theorem updateAssignment_commute_of_ne {M : SigmaModel} (rho : Assignment M)
    {left right : SortTag} {leftIdx rightIdx : Nat}
    (leftValue : M.Carrier left) (rightValue : M.Carrier right)
    (hNe : Not (And (left = right) (leftIdx = rightIdx))) :
    updateAssignment (updateAssignment rho left leftIdx leftValue)
        right rightIdx rightValue =
      updateAssignment (updateAssignment rho right rightIdx rightValue)
        left leftIdx leftValue := by
  by_cases hSort : left = right
  · subst hSort
    have hIdxNe : leftIdx ≠ rightIdx := by
      intro hIdx
      exact hNe (And.intro rfl hIdx)
    funext s n
    by_cases hs : s = left
    · subst hs
      by_cases hnLeft : n = leftIdx
      · subst hnLeft
        simp [updateAssignment, hIdxNe]
      · by_cases hnRight : n = rightIdx
        · subst hnRight
          simp [updateAssignment, hIdxNe, hnLeft]
        · simp [updateAssignment, hnLeft, hnRight]
    · simp [updateAssignment, hs]
  · have hRightLeft : right ≠ left := by
      intro h
      exact hSort h.symm
    funext s n
    by_cases hsLeft : s = left
    · subst hsLeft
      simp [updateAssignment, hSort]
    · by_cases hsRight : s = right
      · subst hsRight
        simp [updateAssignment, hRightLeft]
      · simp [updateAssignment, hsLeft, hsRight]

mutual

def AssignmentsAgreeOnTerm {M : SigmaModel}
    (rho sigma : Assignment M) : {s : SortTag} -> Term s -> Prop
  | s, Term.var idx => rho s idx = sigma s idx
  | _, Term.app _ args => AssignmentsAgreeOnArgs rho sigma args

def AssignmentsAgreeOnArgs {M : SigmaModel}
    (rho sigma : Assignment M) :
    {signature : List SortTag} -> Args Term signature -> Prop
  | [], Args.nil => True
  | _ :: _, Args.cons term rest =>
      And (AssignmentsAgreeOnTerm rho sigma term)
        (AssignmentsAgreeOnArgs rho sigma rest)

end

mutual

theorem evalTerm_eq_of_agree {M : SigmaModel}
    {rho sigma : Assignment M} :
    {s : SortTag} -> (term : Term s) ->
      AssignmentsAgreeOnTerm rho sigma term ->
        evalTerm rho term = evalTerm sigma term
  | _, Term.var _, h => h
  | _, Term.app _ args, h => by
      rw [evalTerm, evalTerm, evalArgs_eq_of_agree args h]

theorem evalArgs_eq_of_agree {M : SigmaModel}
    {rho sigma : Assignment M} :
    {signature : List SortTag} -> (args : Args Term signature) ->
      AssignmentsAgreeOnArgs rho sigma args ->
        evalArgs rho args = evalArgs sigma args
  | [], Args.nil, _ => rfl
  | _ :: _, Args.cons term rest, h => by
      rw [evalArgs, evalArgs, evalTerm_eq_of_agree term h.left,
        evalArgs_eq_of_agree rest h.right]

end

def substitutionAssignment {M : SigmaModel} (rho : Assignment M)
    (sigma : Substitution) : Assignment M :=
  fun s idx => evalTerm rho (sigma s idx)

mutual

theorem evalTerm_subst {M : SigmaModel}
    (rho : Assignment M) (sigma : Substitution) :
    {s : SortTag} -> (term : Term s) ->
      evalTerm rho (substTerm sigma term) =
        evalTerm (substitutionAssignment rho sigma) term
  | _, Term.var _ => rfl
  | _, Term.app _ args => by
      rw [substTerm, evalTerm, evalTerm, evalArgs_subst rho sigma args]

theorem evalArgs_subst {M : SigmaModel}
    (rho : Assignment M) (sigma : Substitution) :
    {signature : List SortTag} -> (args : Args Term signature) ->
      evalArgs rho (substArgs sigma args) =
        evalArgs (substitutionAssignment rho sigma) args
  | [], Args.nil => rfl
  | _ :: _, Args.cons term rest => by
      rw [substArgs, evalArgs, evalArgs, evalTerm_subst rho sigma term,
        evalArgs_subst rho sigma rest]

end

def QuantifierFree : Formula -> Prop
  | Formula.truth => True
  | Formula.falsity => True
  | Formula.atom _ _ => True
  | Formula.conj left right => And (QuantifierFree left) (QuantifierFree right)
  | Formula.disj left right => And (QuantifierFree left) (QuantifierFree right)
  | Formula.impl left right => And (QuantifierFree left) (QuantifierFree right)
  | Formula.neg body => QuantifierFree body
  | Formula.forallVar _ _ _ => False
  | Formula.existsVar _ _ _ => False

theorem satisfies_subst_iff_quantifier_free {M : SigmaModel}
    (rho : Assignment M) (sigma : Substitution) :
    (formula : Formula) ->
      QuantifierFree formula ->
        Iff (SatisfiesFormula rho (substFormula sigma formula))
          (SatisfiesFormula (substitutionAssignment rho sigma) formula)
  | Formula.truth, _ =>
      Iff.intro (fun _ => True.intro) (fun _ => True.intro)
  | Formula.falsity, _ =>
      Iff.intro (fun h => h) (fun h => h)
  | Formula.atom p args, _ => by
      rw [substFormula, SatisfiesFormula, SatisfiesFormula,
        evalArgs_subst rho sigma args]
  | Formula.conj left right, h =>
      let hl := satisfies_subst_iff_quantifier_free rho sigma left h.left
      let hr := satisfies_subst_iff_quantifier_free rho sigma right h.right
      Iff.intro
        (fun hs => And.intro (hl.mp hs.left) (hr.mp hs.right))
        (fun hs => And.intro (hl.mpr hs.left) (hr.mpr hs.right))
  | Formula.disj left right, h =>
      let hl := satisfies_subst_iff_quantifier_free rho sigma left h.left
      let hr := satisfies_subst_iff_quantifier_free rho sigma right h.right
      Iff.intro
        (fun hs =>
          Or.elim hs (fun hleft => Or.inl (hl.mp hleft))
            (fun hright => Or.inr (hr.mp hright)))
        (fun hs =>
          Or.elim hs (fun hleft => Or.inl (hl.mpr hleft))
            (fun hright => Or.inr (hr.mpr hright)))
  | Formula.impl left right, h =>
      let hl := satisfies_subst_iff_quantifier_free rho sigma left h.left
      let hr := satisfies_subst_iff_quantifier_free rho sigma right h.right
      Iff.intro
        (fun himp hsleft => hr.mp (himp (hl.mpr hsleft)))
        (fun himp hrleft => hr.mpr (himp (hl.mp hrleft)))
  | Formula.neg body, h =>
      let hb := satisfies_subst_iff_quantifier_free rho sigma body h
      Iff.intro
        (fun hn hs => hn (hb.mpr hs))
        (fun hn hs => hn (hb.mp hs))
  | Formula.forallVar _ _ _, h => False.elim h
  | Formula.existsVar _ _ _, h => False.elim h

def AssignmentsAgreeOnFormula {M : SigmaModel}
    (rho sigma : Assignment M) : Formula -> Prop
  | Formula.truth => True
  | Formula.falsity => True
  | Formula.atom _ args => AssignmentsAgreeOnArgs rho sigma args
  | Formula.conj left right =>
      And (AssignmentsAgreeOnFormula rho sigma left)
        (AssignmentsAgreeOnFormula rho sigma right)
  | Formula.disj left right =>
      And (AssignmentsAgreeOnFormula rho sigma left)
        (AssignmentsAgreeOnFormula rho sigma right)
  | Formula.impl left right =>
      And (AssignmentsAgreeOnFormula rho sigma left)
        (AssignmentsAgreeOnFormula rho sigma right)
  | Formula.neg body => AssignmentsAgreeOnFormula rho sigma body
  | Formula.forallVar s idx body =>
      forall value : M.Carrier s,
        AssignmentsAgreeOnFormula
          (updateAssignment rho s idx value)
          (updateAssignment sigma s idx value)
          body
  | Formula.existsVar s idx body =>
      forall value : M.Carrier s,
        AssignmentsAgreeOnFormula
          (updateAssignment rho s idx value)
          (updateAssignment sigma s idx value)
          body

mutual

theorem assignments_agree_term_refl {M : SigmaModel}
    (rho : Assignment M) :
    {s : SortTag} -> (term : Term s) ->
      AssignmentsAgreeOnTerm rho rho term
  | _, Term.var _ => rfl
  | _, Term.app _ args => assignments_agree_args_refl rho args

theorem assignments_agree_args_refl {M : SigmaModel}
    (rho : Assignment M) :
    {signature : List SortTag} -> (args : Args Term signature) ->
      AssignmentsAgreeOnArgs rho rho args
  | [], Args.nil => True.intro
  | _ :: _, Args.cons term rest =>
      And.intro
        (assignments_agree_term_refl rho term)
        (assignments_agree_args_refl rho rest)

end

theorem assignments_agree_formula_refl {M : SigmaModel}
    (rho : Assignment M) :
    (formula : Formula) -> AssignmentsAgreeOnFormula rho rho formula
  | Formula.truth => True.intro
  | Formula.falsity => True.intro
  | Formula.atom _ args => assignments_agree_args_refl rho args
  | Formula.conj left right =>
      And.intro
        (assignments_agree_formula_refl rho left)
        (assignments_agree_formula_refl rho right)
  | Formula.disj left right =>
      And.intro
        (assignments_agree_formula_refl rho left)
        (assignments_agree_formula_refl rho right)
  | Formula.impl left right =>
      And.intro
        (assignments_agree_formula_refl rho left)
        (assignments_agree_formula_refl rho right)
  | Formula.neg body => assignments_agree_formula_refl rho body
  | Formula.forallVar s idx body =>
      fun value =>
        assignments_agree_formula_refl
          (updateAssignment rho s idx value) body
  | Formula.existsVar s idx body =>
      fun value =>
        assignments_agree_formula_refl
          (updateAssignment rho s idx value) body

mutual

theorem term_agrees_of_free_var_agreement {M : SigmaModel}
    {rho sigma : Assignment M} :
    {s : SortTag} -> (term : Term s) ->
      (forall target idx, TermHasVar target idx term ->
        rho target idx = sigma target idx) ->
        AssignmentsAgreeOnTerm rho sigma term
  | s, Term.var idx, hAgree =>
      hAgree s idx (And.intro rfl rfl)
  | _, Term.app _ args, hAgree =>
      args_agrees_of_free_var_agreement args hAgree

theorem args_agrees_of_free_var_agreement {M : SigmaModel}
    {rho sigma : Assignment M} :
    {signature : List SortTag} -> (args : Args Term signature) ->
      (forall target idx, ArgsHaveVar target idx args ->
        rho target idx = sigma target idx) ->
        AssignmentsAgreeOnArgs rho sigma args
  | [], Args.nil, _ => True.intro
  | _ :: _, Args.cons term rest, hAgree =>
      And.intro
        (term_agrees_of_free_var_agreement term
          (fun target idx hVar => hAgree target idx (Or.inl hVar)))
        (args_agrees_of_free_var_agreement rest
          (fun target idx hVar => hAgree target idx (Or.inr hVar)))

end

def FormulaFreeVariablesAgree {M : SigmaModel}
    (rho sigma : Assignment M) (formula : Formula) : Prop :=
  forall target idx, FormulaHasFreeVar target idx formula ->
    rho target idx = sigma target idx

def FormulaClosed (formula : Formula) : Prop :=
  forall target idx, Not (FormulaHasFreeVar target idx formula)

theorem formula_agrees_of_free_var_agreement {M : SigmaModel}
    {rho sigma : Assignment M} :
    (formula : Formula) ->
      FormulaFreeVariablesAgree rho sigma formula ->
        AssignmentsAgreeOnFormula rho sigma formula
  | Formula.truth, _ => True.intro
  | Formula.falsity, _ => True.intro
  | Formula.atom _ args, hAgree =>
      args_agrees_of_free_var_agreement args hAgree
  | Formula.conj left right, hAgree =>
      And.intro
        (formula_agrees_of_free_var_agreement left
          (fun target idx hVar => hAgree target idx (Or.inl hVar)))
        (formula_agrees_of_free_var_agreement right
          (fun target idx hVar => hAgree target idx (Or.inr hVar)))
  | Formula.disj left right, hAgree =>
      And.intro
        (formula_agrees_of_free_var_agreement left
          (fun target idx hVar => hAgree target idx (Or.inl hVar)))
        (formula_agrees_of_free_var_agreement right
          (fun target idx hVar => hAgree target idx (Or.inr hVar)))
  | Formula.impl left right, hAgree =>
      And.intro
        (formula_agrees_of_free_var_agreement left
          (fun target idx hVar => hAgree target idx (Or.inl hVar)))
        (formula_agrees_of_free_var_agreement right
          (fun target idx hVar => hAgree target idx (Or.inr hVar)))
  | Formula.neg body, hAgree =>
      formula_agrees_of_free_var_agreement body hAgree
  | Formula.forallVar s binderIdx body, hAgree =>
      fun value =>
        formula_agrees_of_free_var_agreement body
          (fun target idx hVar => by
            by_cases hBinder : And (s = target) (binderIdx = idx)
            · rcases hBinder with ⟨hs, hidx⟩
              subst hs
              subst hidx
              simp [updateAssignment]
            · have hBase : rho target idx = sigma target idx :=
                hAgree target idx
                  (by
                    simp [FormulaHasFreeVar, hBinder, hVar])
              by_cases hs : target = s
              · subst hs
                have hIdxNe : idx ≠ binderIdx := by
                  intro hIdx
                  apply hBinder
                  exact And.intro rfl hIdx.symm
                simp [updateAssignment, hIdxNe, hBase]
              · simp [updateAssignment, hs, hBase])
  | Formula.existsVar s binderIdx body, hAgree =>
      fun value =>
        formula_agrees_of_free_var_agreement body
          (fun target idx hVar => by
            by_cases hBinder : And (s = target) (binderIdx = idx)
            · rcases hBinder with ⟨hs, hidx⟩
              subst hs
              subst hidx
              simp [updateAssignment]
            · have hBase : rho target idx = sigma target idx :=
                hAgree target idx
                  (by
                    simp [FormulaHasFreeVar, hBinder, hVar])
              by_cases hs : target = s
              · subst hs
                have hIdxNe : idx ≠ binderIdx := by
                  intro hIdx
                  apply hBinder
                  exact And.intro rfl hIdx.symm
                simp [updateAssignment, hIdxNe, hBase]
              · simp [updateAssignment, hs, hBase])

theorem closed_formula_assignments_agree {M : SigmaModel}
    (rho sigma : Assignment M) (formula : Formula)
    (hClosed : FormulaClosed formula) :
    AssignmentsAgreeOnFormula rho sigma formula :=
  formula_agrees_of_free_var_agreement formula
    (fun target idx hVar => False.elim (hClosed target idx hVar))

theorem satisfiesFormula_iff_of_agree {M : SigmaModel}
    {rho sigma : Assignment M} :
    (formula : Formula) ->
      AssignmentsAgreeOnFormula rho sigma formula ->
        Iff (SatisfiesFormula rho formula) (SatisfiesFormula sigma formula)
  | Formula.truth, _ => Iff.intro (fun _ => True.intro) (fun _ => True.intro)
  | Formula.falsity, _ => Iff.intro (fun h => h) (fun h => h)
  | Formula.atom p args, h => by
      rw [SatisfiesFormula, SatisfiesFormula, evalArgs_eq_of_agree args h]
  | Formula.conj left right, h =>
      let hl := satisfiesFormula_iff_of_agree left h.left
      let hr := satisfiesFormula_iff_of_agree right h.right
      Iff.intro
        (fun hs => And.intro (hl.mp hs.left) (hr.mp hs.right))
        (fun hs => And.intro (hl.mpr hs.left) (hr.mpr hs.right))
  | Formula.disj left right, h =>
      let hl := satisfiesFormula_iff_of_agree left h.left
      let hr := satisfiesFormula_iff_of_agree right h.right
      Iff.intro
        (fun hs =>
          Or.elim hs (fun hleft => Or.inl (hl.mp hleft))
            (fun hright => Or.inr (hr.mp hright)))
        (fun hs =>
          Or.elim hs (fun hleft => Or.inl (hl.mpr hleft))
            (fun hright => Or.inr (hr.mpr hright)))
  | Formula.impl left right, h =>
      let hl := satisfiesFormula_iff_of_agree left h.left
      let hr := satisfiesFormula_iff_of_agree right h.right
      Iff.intro
        (fun himp hsleft => hr.mp (himp (hl.mpr hsleft)))
        (fun himp hrleft => hr.mpr (himp (hl.mp hrleft)))
  | Formula.neg body, h =>
      let hb := satisfiesFormula_iff_of_agree body h
      Iff.intro
        (fun hn hs => hn (hb.mpr hs))
        (fun hn hs => hn (hb.mp hs))
  | Formula.forallVar s idx body, h =>
      Iff.intro
        (fun hall value =>
          (satisfiesFormula_iff_of_agree body (h value)).mp (hall value))
        (fun hall value =>
          (satisfiesFormula_iff_of_agree body (h value)).mpr (hall value))
  | Formula.existsVar s idx body, h =>
      Iff.intro
        (fun hex =>
          Exists.elim hex
            (fun value hbody =>
              Exists.intro value
                ((satisfiesFormula_iff_of_agree body (h value)).mp hbody)))
        (fun hex =>
          Exists.elim hex
            (fun value hbody =>
              Exists.intro value
                ((satisfiesFormula_iff_of_agree body (h value)).mpr hbody)))

theorem closed_formula_satisfaction_invariant {M : SigmaModel}
    (rho sigma : Assignment M) (formula : Formula)
    (hClosed : FormulaClosed formula) :
    Iff (SatisfiesFormula rho formula) (SatisfiesFormula sigma formula) :=
  satisfiesFormula_iff_of_agree formula
    (closed_formula_assignments_agree rho sigma formula hClosed)

def PremisesClosed (premises : List Formula) : Prop :=
  forall formula, List.Mem formula premises -> FormulaClosed formula

theorem premises_closed_nil : PremisesClosed [] := by
  intro _ hMem
  cases hMem

theorem premises_closed_cons {formula : Formula} {rest : List Formula}
    (hFormula : FormulaClosed formula)
    (hRest : PremisesClosed rest) :
    PremisesClosed (formula :: rest) := by
  intro candidate hMem
  cases hMem with
  | head =>
      exact hFormula
  | tail _ hTail =>
      exact hRest candidate hTail

theorem closed_premises_satisfaction_invariant {M : SigmaModel}
    (rho sigma : Assignment M) :
    (premises : List Formula) ->
      PremisesClosed premises ->
        Iff (SatisfiesAll rho premises) (SatisfiesAll sigma premises)
  | [], _ => Iff.intro (fun _ => True.intro) (fun _ => True.intro)
  | formula :: rest, hClosed =>
      let hHead : FormulaClosed formula :=
        hClosed formula (List.Mem.head rest)
      let hTail : PremisesClosed rest :=
        fun candidate hMem =>
          hClosed candidate (List.Mem.tail formula hMem)
      let hFormulaIff :=
        closed_formula_satisfaction_invariant rho sigma formula hHead
      let hRestIff :=
        closed_premises_satisfaction_invariant rho sigma rest hTail
      Iff.intro
        (fun hAll => And.intro
          (hFormulaIff.mp hAll.left)
          (hRestIff.mp hAll.right))
        (fun hAll => And.intro
          (hFormulaIff.mpr hAll.left)
          (hRestIff.mpr hAll.right))

mutual

theorem term_agrees_update_of_not_free {M : SigmaModel}
    (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    {s : SortTag} -> (term : Term s) ->
      Not (TermHasVar target idx term) ->
        AssignmentsAgreeOnTerm rho
          (updateAssignment rho target idx value) term
  | s, Term.var n, hNot => by
      by_cases hs : s = target
      · subst hs
        by_cases hn : n = idx
        · subst hn
          exact False.elim (hNot (And.intro rfl rfl))
        · simp [AssignmentsAgreeOnTerm, TermHasVar, updateAssignment, hn]
      · simp [AssignmentsAgreeOnTerm, TermHasVar, updateAssignment, hs]
  | _, Term.app _ args, hNot =>
      args_agrees_update_of_not_free rho target idx value args hNot

theorem args_agrees_update_of_not_free {M : SigmaModel}
    (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    {signature : List SortTag} -> (args : Args Term signature) ->
      Not (ArgsHaveVar target idx args) ->
        AssignmentsAgreeOnArgs rho
          (updateAssignment rho target idx value) args
  | [], Args.nil, _ => True.intro
  | _ :: _, Args.cons term rest, hNot =>
      And.intro
        (term_agrees_update_of_not_free rho target idx value term
          (fun hTerm => hNot (Or.inl hTerm)))
        (args_agrees_update_of_not_free rho target idx value rest
          (fun hRest => hNot (Or.inr hRest)))

end

theorem quantifier_free_formula_agrees_update_of_not_free {M : SigmaModel}
    (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    (formula : Formula) ->
      QuantifierFree formula ->
        Not (FormulaHasFreeVar target idx formula) ->
          AssignmentsAgreeOnFormula rho
            (updateAssignment rho target idx value) formula
  | Formula.truth, _, _ => True.intro
  | Formula.falsity, _, _ => True.intro
  | Formula.atom _ args, _, hNot =>
      args_agrees_update_of_not_free rho target idx value args hNot
  | Formula.conj left right, hQf, hNot =>
      And.intro
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value left hQf.left (fun hLeft => hNot (Or.inl hLeft)))
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value right hQf.right (fun hRight => hNot (Or.inr hRight)))
  | Formula.disj left right, hQf, hNot =>
      And.intro
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value left hQf.left (fun hLeft => hNot (Or.inl hLeft)))
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value right hQf.right (fun hRight => hNot (Or.inr hRight)))
  | Formula.impl left right, hQf, hNot =>
      And.intro
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value left hQf.left (fun hLeft => hNot (Or.inl hLeft)))
        (quantifier_free_formula_agrees_update_of_not_free rho target idx
          value right hQf.right (fun hRight => hNot (Or.inr hRight)))
  | Formula.neg body, hQf, hNot =>
      quantifier_free_formula_agrees_update_of_not_free rho target idx value
        body hQf hNot
  | Formula.forallVar _ _ _, hQf, _ => False.elim hQf
  | Formula.existsVar _ _ _, hQf, _ => False.elim hQf

theorem quantifier_free_satisfaction_stable_update_of_not_free
    {M : SigmaModel} (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) (formula : Formula)
    (hQf : QuantifierFree formula)
    (hNotFree : Not (FormulaHasFreeVar target idx formula)) :
    Iff (SatisfiesFormula rho formula)
      (SatisfiesFormula (updateAssignment rho target idx value) formula) :=
  satisfiesFormula_iff_of_agree formula
    (quantifier_free_formula_agrees_update_of_not_free rho target idx value
      formula hQf hNotFree)

theorem formula_agrees_update_of_not_free {M : SigmaModel}
    (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) :
    (formula : Formula) ->
      Not (FormulaHasFreeVar target idx formula) ->
        AssignmentsAgreeOnFormula rho
          (updateAssignment rho target idx value) formula
  | Formula.truth, _ => True.intro
  | Formula.falsity, _ => True.intro
  | Formula.atom _ args, hNot =>
      args_agrees_update_of_not_free rho target idx value args hNot
  | Formula.conj left right, hNot =>
      And.intro
        (formula_agrees_update_of_not_free rho target idx value left
          (fun hLeft => hNot (Or.inl hLeft)))
        (formula_agrees_update_of_not_free rho target idx value right
          (fun hRight => hNot (Or.inr hRight)))
  | Formula.disj left right, hNot =>
      And.intro
        (formula_agrees_update_of_not_free rho target idx value left
          (fun hLeft => hNot (Or.inl hLeft)))
        (formula_agrees_update_of_not_free rho target idx value right
          (fun hRight => hNot (Or.inr hRight)))
  | Formula.impl left right, hNot =>
      And.intro
        (formula_agrees_update_of_not_free rho target idx value left
          (fun hLeft => hNot (Or.inl hLeft)))
        (formula_agrees_update_of_not_free rho target idx value right
          (fun hRight => hNot (Or.inr hRight)))
  | Formula.neg body, hNot =>
      formula_agrees_update_of_not_free rho target idx value body hNot
  | Formula.forallVar s binderIdx body, hNot =>
      fun binderValue => by
        by_cases hSame : And (s = target) (binderIdx = idx)
        · rcases hSame with ⟨hs, hidx⟩
          subst hs
          subst hidx
          have hEq :
              updateAssignment
                  (updateAssignment rho s binderIdx value) s binderIdx
                    binderValue =
                updateAssignment rho s binderIdx binderValue :=
            updateAssignment_shadow_same rho s binderIdx value binderValue
          rw [hEq]
          exact assignments_agree_formula_refl
            (updateAssignment rho s binderIdx binderValue) body
        · have hBodyNot : Not (FormulaHasFreeVar target idx body) := by
            intro hBody
            apply hNot
            simp [FormulaHasFreeVar, hSame, hBody]
          have hAgree :=
            formula_agrees_update_of_not_free
              (updateAssignment rho s binderIdx binderValue) target idx value
              body hBodyNot
          have hComm :
              updateAssignment
                  (updateAssignment rho s binderIdx binderValue) target idx
                    value =
                updateAssignment
                  (updateAssignment rho target idx value) s binderIdx
                    binderValue :=
            updateAssignment_commute_of_ne rho binderValue value hSame
          rw [hComm] at hAgree
          exact hAgree
  | Formula.existsVar s binderIdx body, hNot =>
      fun binderValue => by
        by_cases hSame : And (s = target) (binderIdx = idx)
        · rcases hSame with ⟨hs, hidx⟩
          subst hs
          subst hidx
          have hEq :
              updateAssignment
                  (updateAssignment rho s binderIdx value) s binderIdx
                    binderValue =
                updateAssignment rho s binderIdx binderValue :=
            updateAssignment_shadow_same rho s binderIdx value binderValue
          rw [hEq]
          exact assignments_agree_formula_refl
            (updateAssignment rho s binderIdx binderValue) body
        · have hBodyNot : Not (FormulaHasFreeVar target idx body) := by
            intro hBody
            apply hNot
            simp [FormulaHasFreeVar, hSame, hBody]
          have hAgree :=
            formula_agrees_update_of_not_free
              (updateAssignment rho s binderIdx binderValue) target idx value
              body hBodyNot
          have hComm :
              updateAssignment
                  (updateAssignment rho s binderIdx binderValue) target idx
                    value =
                updateAssignment
                  (updateAssignment rho target idx value) s binderIdx
                    binderValue :=
            updateAssignment_commute_of_ne rho binderValue value hSame
          rw [hComm] at hAgree
          exact hAgree

theorem satisfaction_stable_update_of_not_free
    {M : SigmaModel} (rho : Assignment M) (target : SortTag) (idx : Nat)
    (value : M.Carrier target) (formula : Formula)
    (hNotFree : Not (FormulaHasFreeVar target idx formula)) :
    Iff (SatisfiesFormula rho formula)
      (SatisfiesFormula (updateAssignment rho target idx value) formula) :=
  satisfiesFormula_iff_of_agree formula
    (formula_agrees_update_of_not_free rho target idx value formula hNotFree)

theorem satisfies_truth {M : SigmaModel} (rho : Assignment M) :
    SatisfiesFormula rho Formula.truth :=
  True.intro

theorem not_satisfies_falsity {M : SigmaModel} (rho : Assignment M) :
    Not (SatisfiesFormula rho Formula.falsity) := by
  intro h
  exact h

theorem satisfies_conj_intro {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (hl : SatisfiesFormula rho left)
    (hr : SatisfiesFormula rho right) :
    SatisfiesFormula rho (Formula.conj left right) :=
  And.intro hl hr

theorem satisfies_conj_left {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (h : SatisfiesFormula rho (Formula.conj left right)) :
    SatisfiesFormula rho left :=
  h.left

theorem satisfies_conj_right {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (h : SatisfiesFormula rho (Formula.conj left right)) :
    SatisfiesFormula rho right :=
  h.right

theorem satisfies_disj_left {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (h : SatisfiesFormula rho left) :
    SatisfiesFormula rho (Formula.disj left right) :=
  Or.inl h

theorem satisfies_disj_right {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (h : SatisfiesFormula rho right) :
    SatisfiesFormula rho (Formula.disj left right) :=
  Or.inr h

theorem satisfies_impl_elim {M : SigmaModel} {rho : Assignment M}
    {left right : Formula}
    (himp : SatisfiesFormula rho (Formula.impl left right))
    (hleft : SatisfiesFormula rho left) :
    SatisfiesFormula rho right :=
  himp hleft

theorem satisfies_forall_elim {M : SigmaModel} {rho : Assignment M}
    {s : SortTag} {idx : Nat} {body : Formula}
    (h : SatisfiesFormula rho (Formula.forallVar s idx body))
    (value : M.Carrier s) :
    SatisfiesFormula (updateAssignment rho s idx value) body :=
  h value

theorem satisfies_exists_intro {M : SigmaModel} {rho : Assignment M}
    {s : SortTag} {idx : Nat} {body : Formula}
    (value : M.Carrier s)
    (h : SatisfiesFormula (updateAssignment rho s idx value) body) :
    SatisfiesFormula rho (Formula.existsVar s idx body) :=
  Exists.intro value h

theorem satisfies_all_nil {M : SigmaModel} (rho : Assignment M) :
    SatisfiesAll rho [] :=
  True.intro

theorem satisfies_all_cons_intro {M : SigmaModel} {rho : Assignment M}
    {formula : Formula} {rest : List Formula}
    (hf : SatisfiesFormula rho formula)
    (hr : SatisfiesAll rho rest) :
    SatisfiesAll rho (formula :: rest) :=
  And.intro hf hr

theorem satisfies_all_cons_head {M : SigmaModel} {rho : Assignment M}
    {formula : Formula} {rest : List Formula}
    (h : SatisfiesAll rho (formula :: rest)) :
    SatisfiesFormula rho formula :=
  h.left

theorem satisfies_all_cons_tail {M : SigmaModel} {rho : Assignment M}
    {formula : Formula} {rest : List Formula}
    (h : SatisfiesAll rho (formula :: rest)) :
    SatisfiesAll rho rest :=
  h.right

theorem semantically_entails_refl (formula : Formula) :
    SemanticallyEntails [formula] formula := by
  intro _ _ h
  exact h.left

theorem semantically_entails_truth (premises : List Formula) :
    SemanticallyEntails premises Formula.truth := by
  intro _ _ _
  exact True.intro

theorem semantically_entails_trans {premises : List Formula}
    {middle conclusion : Formula}
    (h1 : SemanticallyEntails premises middle)
    (h2 : SemanticallyEntails [middle] conclusion) :
    SemanticallyEntails premises conclusion := by
  intro M rho hp
  exact h2 M rho (And.intro (h1 M rho hp) True.intro)

theorem satisfies_all_append_left {M : SigmaModel} {rho : Assignment M}
    {left right : List Formula}
    (h : SatisfiesAll rho (left ++ right)) :
    SatisfiesAll rho left := by
  induction left with
  | nil =>
      exact True.intro
  | cons _ rest ih =>
      exact And.intro h.left (ih h.right)

theorem satisfies_all_append_right {M : SigmaModel} {rho : Assignment M}
    {left right : List Formula}
    (h : SatisfiesAll rho (left ++ right)) :
    SatisfiesAll rho right := by
  induction left with
  | nil =>
      exact h
  | cons _ rest ih =>
      exact ih h.right

theorem satisfies_all_append_intro {M : SigmaModel} {rho : Assignment M}
    {left right : List Formula}
    (hl : SatisfiesAll rho left)
    (hr : SatisfiesAll rho right) :
    SatisfiesAll rho (left ++ right) := by
  induction left with
  | nil =>
      exact hr
  | cons _ rest ih =>
      exact And.intro hl.left (ih hl.right)

theorem semantically_entails_append_monotone_right
    {premises extra : List Formula} {conclusion : Formula}
    (h : SemanticallyEntails premises conclusion) :
    SemanticallyEntails (premises ++ extra) conclusion := by
  intro M rho hp
  exact h M rho (satisfies_all_append_left hp)

theorem semantically_entails_append_monotone_left
    {extra premises : List Formula} {conclusion : Formula}
    (h : SemanticallyEntails premises conclusion) :
    SemanticallyEntails (extra ++ premises) conclusion := by
  intro M rho hp
  exact h M rho (satisfies_all_append_right hp)

end Paralogic
