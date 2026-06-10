import Paralogic.CoreTypes

/-!
Many-sorted model semantics for the Paralogic / ISFT core.

This module starts Bottleneck 1 from the controlling audit.  It does not
complete Paralogic, but it replaces the one-object Boolean world with a typed
signature, model class, interpretation functions, formula satisfaction, and
semantic definitions for ISF, M8, ValidInsight, normative bridges, and
empirical-validation boundaries.
-/

namespace Paralogic

structure FunctionArity where
  domain : List SortTag
  codomain : SortTag
  deriving DecidableEq, Repr

structure PredicateArity where
  domain : List SortTag
  deriving DecidableEq, Repr

inductive FunctionSymbol where
  | outputInstitution
  | outputContext
  | claimEvidence
  | claimContext
  | evaluatorContext
  | validationTarget
  | bridgeTarget
  deriving DecidableEq, Repr

def functionArity : FunctionSymbol -> FunctionArity
  | FunctionSymbol.outputInstitution =>
      { domain := [SortTag.symbolicOutput], codomain := SortTag.institution }
  | FunctionSymbol.outputContext =>
      { domain := [SortTag.symbolicOutput], codomain := SortTag.context }
  | FunctionSymbol.claimEvidence =>
      { domain := [SortTag.claim], codomain := SortTag.evidenceSet }
  | FunctionSymbol.claimContext =>
      { domain := [SortTag.claim], codomain := SortTag.context }
  | FunctionSymbol.evaluatorContext =>
      { domain := [SortTag.evaluator], codomain := SortTag.context }
  | FunctionSymbol.validationTarget =>
      { domain := [SortTag.empiricalValidationObject],
        codomain := SortTag.claim }
  | FunctionSymbol.bridgeTarget =>
      { domain := [SortTag.normativeBridge], codomain := SortTag.claim }

inductive PredicateSymbol where
  | uses
  | claims
  | supports
  | adequate
  | supportDegraded
  | treatsAsAdequate
  | contradictionPresent
  | contradictionAddressed
  | candidateInsight
  | evaluatorAccepts
  | licensedTransition
  | nonTrivialTransformation
  | noHigherOrderDefeater
  | generativityMinimal
  | directionalNonEquivalence
  | powerRelevant
  | powerValidityDependence
  | powerOmitted
  | harmBridge
  | responsibilityBridge
  | repairObligationBridge
  | accountabilityBridge
  | legalIllegitimacyBridge
  | governanceLegitimacyBridge
  | moralGuiltBridge
  | empiricalValidation
  | constructValid
  | reliabilityTested
  | externallyReplicated
  deriving DecidableEq, Repr

def predicateArity : PredicateSymbol -> PredicateArity
  | PredicateSymbol.uses =>
      { domain := [SortTag.institution, SortTag.symbolicOutput] }
  | PredicateSymbol.claims =>
      { domain := [SortTag.institution, SortTag.symbolicOutput, SortTag.claim] }
  | PredicateSymbol.supports =>
      { domain := [SortTag.evidenceSet, SortTag.claim] }
  | PredicateSymbol.adequate =>
      { domain := [SortTag.evidenceSet, SortTag.context, SortTag.claim] }
  | PredicateSymbol.supportDegraded =>
      { domain := [SortTag.evidenceSet, SortTag.context, SortTag.claim] }
  | PredicateSymbol.treatsAsAdequate =>
      { domain :=
          [SortTag.institution, SortTag.symbolicOutput, SortTag.claim,
            SortTag.context] }
  | PredicateSymbol.contradictionPresent =>
      { domain := [SortTag.frame, SortTag.context, SortTag.claim] }
  | PredicateSymbol.contradictionAddressed =>
      { domain := [SortTag.candidateInsight, SortTag.claim] }
  | PredicateSymbol.candidateInsight =>
      { domain := [SortTag.candidateInsight] }
  | PredicateSymbol.evaluatorAccepts =>
      { domain := [SortTag.evaluator, SortTag.candidateInsight] }
  | PredicateSymbol.licensedTransition =>
      { domain := [SortTag.candidateInsight, SortTag.frame, SortTag.frame] }
  | PredicateSymbol.nonTrivialTransformation =>
      { domain := [SortTag.candidateInsight, SortTag.frame, SortTag.frame] }
  | PredicateSymbol.noHigherOrderDefeater =>
      { domain := [SortTag.evaluator, SortTag.candidateInsight] }
  | PredicateSymbol.generativityMinimal =>
      { domain := [SortTag.candidateInsight] }
  | PredicateSymbol.directionalNonEquivalence =>
      { domain := [SortTag.frame, SortTag.frame] }
  | PredicateSymbol.powerRelevant =>
      { domain := [SortTag.institution, SortTag.affectedGroup] }
  | PredicateSymbol.powerValidityDependence =>
      { domain := [SortTag.institution, SortTag.symbolicOutput,
          SortTag.powerCondition] }
  | PredicateSymbol.powerOmitted =>
      { domain := [SortTag.institution, SortTag.symbolicOutput,
          SortTag.powerCondition] }
  | PredicateSymbol.harmBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution,
          SortTag.affectedGroup] }
  | PredicateSymbol.responsibilityBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution] }
  | PredicateSymbol.repairObligationBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution,
          SortTag.affectedGroup] }
  | PredicateSymbol.accountabilityBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution] }
  | PredicateSymbol.legalIllegitimacyBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution] }
  | PredicateSymbol.governanceLegitimacyBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution] }
  | PredicateSymbol.moralGuiltBridge =>
      { domain := [SortTag.normativeBridge, SortTag.institution] }
  | PredicateSymbol.empiricalValidation =>
      { domain := [SortTag.empiricalValidationObject, SortTag.claim] }
  | PredicateSymbol.constructValid =>
      { domain := [SortTag.empiricalValidationObject] }
  | PredicateSymbol.reliabilityTested =>
      { domain := [SortTag.empiricalValidationObject] }
  | PredicateSymbol.externallyReplicated =>
      { domain := [SortTag.empiricalValidationObject] }

inductive Args (Carrier : SortTag -> Type) : List SortTag -> Type where
  | nil : Args Carrier []
  | cons {s : SortTag} {rest : List SortTag} :
      Carrier s -> Args Carrier rest -> Args Carrier (s :: rest)

namespace Args

def map {A B : SortTag -> Type}
    (f : {s : SortTag} -> A s -> B s) :
    {signature : List SortTag} -> Args A signature -> Args B signature
  | [], Args.nil => Args.nil
  | _ :: _, Args.cons x xs => Args.cons (f x) (map f xs)

theorem map_id {A : SortTag -> Type} :
    {signature : List SortTag} ->
      (args : Args A signature) ->
        map (fun {s} (x : A s) => x) args = args
  | [], Args.nil => rfl
  | _ :: _, Args.cons _ xs => by
      rw [map, map_id xs]

theorem map_comp {A B C : SortTag -> Type}
    (f : {s : SortTag} -> A s -> B s)
    (g : {s : SortTag} -> B s -> C s) :
    {signature : List SortTag} ->
      (args : Args A signature) ->
        map g (map f args) = map (fun {s} (x : A s) => g (f x)) args
  | [], Args.nil => rfl
  | _ :: _, Args.cons _ xs => by
      rw [map, map, map, map_comp f g xs]

end Args

structure SigmaModel : Type 1 where
  Carrier : SortTag -> Type
  interpFunction :
    (f : FunctionSymbol) ->
      Args Carrier ((functionArity f).domain) ->
      Carrier ((functionArity f).codomain)
  interpPredicate :
    (p : PredicateSymbol) ->
      Args Carrier ((predicateArity p).domain) ->
      Prop

def Assignment (M : SigmaModel) : Type :=
  (s : SortTag) -> Nat -> M.Carrier s

def updateAssignment {M : SigmaModel} (rho : Assignment M)
    (target : SortTag) (idx : Nat) (value : M.Carrier target) :
    Assignment M :=
  fun s n =>
    if h : s = target then
      if hn : n = idx then
        by
          subst h
          exact value
      else
        rho s n
    else
      rho s n

theorem updateAssignment_same {M : SigmaModel} (rho : Assignment M)
    (target : SortTag) (idx : Nat) (value : M.Carrier target) :
    updateAssignment rho target idx value target idx = value := by
  simp [updateAssignment]

theorem updateAssignment_other_index {M : SigmaModel} (rho : Assignment M)
    (target : SortTag) (idx other : Nat) (value : M.Carrier target)
    (hneq : other ≠ idx) :
    updateAssignment rho target idx value target other = rho target other := by
  simp [updateAssignment, hneq]

inductive Term : SortTag -> Type where
  | var {s : SortTag} : Nat -> Term s
  | app (f : FunctionSymbol) :
      Args Term ((functionArity f).domain) ->
      Term ((functionArity f).codomain)

def Substitution : Type :=
  (s : SortTag) -> Nat -> Term s

def identitySubstitution : Substitution :=
  fun _ n => Term.var n

def maskSubstitution (target : SortTag) (idx : Nat)
    (sigma : Substitution) : Substitution :=
  fun s n =>
    if h : s = target then
      if hn : n = idx then
        by
          subst h
          exact Term.var idx
      else
        sigma s n
    else
      sigma s n

theorem maskSubstitution_same (target : SortTag) (idx : Nat)
    (sigma : Substitution) :
    maskSubstitution target idx sigma target idx = Term.var idx := by
  simp [maskSubstitution]

theorem maskSubstitution_other_index (target : SortTag) (idx other : Nat)
    (sigma : Substitution) (hneq : other ≠ idx) :
    maskSubstitution target idx sigma target other = sigma target other := by
  simp [maskSubstitution, hneq]

mutual

def substTerm (sigma : Substitution) : {s : SortTag} -> Term s -> Term s
  | s, Term.var n => sigma s n
  | _, Term.app f args => Term.app f (substArgs sigma args)

def substArgs (sigma : Substitution) :
    {signature : List SortTag} ->
      Args Term signature -> Args Term signature
  | [], Args.nil => Args.nil
  | _ :: _, Args.cons x xs =>
      Args.cons (substTerm sigma x) (substArgs sigma xs)

end

theorem substTerm_var (sigma : Substitution) (s : SortTag) (idx : Nat) :
    substTerm sigma (Term.var (s := s) idx) = sigma s idx := rfl

mutual

def TermHasVar (target : SortTag) (idx : Nat) :
    {s : SortTag} -> Term s -> Prop
  | s, Term.var n => And (s = target) (n = idx)
  | _, Term.app _ args => ArgsHaveVar target idx args

def ArgsHaveVar (target : SortTag) (idx : Nat) :
    {signature : List SortTag} -> Args Term signature -> Prop
  | [], Args.nil => False
  | _ :: _, Args.cons x xs =>
      Or (TermHasVar target idx x) (ArgsHaveVar target idx xs)

end

mutual

def evalTerm {M : SigmaModel} (rho : Assignment M) :
    {s : SortTag} -> Term s -> M.Carrier s
  | s, Term.var n => rho s n
  | _, Term.app f args => M.interpFunction f (evalArgs rho args)

def evalArgs {M : SigmaModel} (rho : Assignment M) :
    {signature : List SortTag} ->
      Args Term signature -> Args M.Carrier signature
  | [], Args.nil => Args.nil
  | _ :: _, Args.cons x xs =>
      Args.cons (evalTerm rho x) (evalArgs rho xs)

end

inductive Formula where
  | truth
  | falsity
  | atom (p : PredicateSymbol) :
      Args Term ((predicateArity p).domain) -> Formula
  | conj : Formula -> Formula -> Formula
  | disj : Formula -> Formula -> Formula
  | impl : Formula -> Formula -> Formula
  | neg : Formula -> Formula
  | forallVar : SortTag -> Nat -> Formula -> Formula
  | existsVar : SortTag -> Nat -> Formula -> Formula

def substFormula (sigma : Substitution) : Formula -> Formula
  | Formula.truth => Formula.truth
  | Formula.falsity => Formula.falsity
  | Formula.atom p args => Formula.atom p (substArgs sigma args)
  | Formula.conj left right =>
      Formula.conj (substFormula sigma left) (substFormula sigma right)
  | Formula.disj left right =>
      Formula.disj (substFormula sigma left) (substFormula sigma right)
  | Formula.impl left right =>
      Formula.impl (substFormula sigma left) (substFormula sigma right)
  | Formula.neg body => Formula.neg (substFormula sigma body)
  | Formula.forallVar s n body =>
      Formula.forallVar s n (substFormula (maskSubstitution s n sigma) body)
  | Formula.existsVar s n body =>
      Formula.existsVar s n (substFormula (maskSubstitution s n sigma) body)

theorem substFormula_truth (sigma : Substitution) :
    substFormula sigma Formula.truth = Formula.truth := rfl

theorem substFormula_falsity (sigma : Substitution) :
    substFormula sigma Formula.falsity = Formula.falsity := rfl

def FormulaHasFreeVar (target : SortTag) (idx : Nat) : Formula -> Prop
  | Formula.truth => False
  | Formula.falsity => False
  | Formula.atom _ args => ArgsHaveVar target idx args
  | Formula.conj left right =>
      Or (FormulaHasFreeVar target idx left) (FormulaHasFreeVar target idx right)
  | Formula.disj left right =>
      Or (FormulaHasFreeVar target idx left) (FormulaHasFreeVar target idx right)
  | Formula.impl left right =>
      Or (FormulaHasFreeVar target idx left) (FormulaHasFreeVar target idx right)
  | Formula.neg body => FormulaHasFreeVar target idx body
  | Formula.forallVar s n body =>
      if _h : And (s = target) (n = idx) then
        False
      else
        FormulaHasFreeVar target idx body
  | Formula.existsVar s n body =>
      if _h : And (s = target) (n = idx) then
        False
      else
        FormulaHasFreeVar target idx body

def SatisfiesFormula {M : SigmaModel} (rho : Assignment M) :
    Formula -> Prop
  | Formula.truth => True
  | Formula.falsity => False
  | Formula.atom p args =>
      M.interpPredicate p (evalArgs rho args)
  | Formula.conj left right =>
      And (SatisfiesFormula rho left) (SatisfiesFormula rho right)
  | Formula.disj left right =>
      Or (SatisfiesFormula rho left) (SatisfiesFormula rho right)
  | Formula.impl left right =>
      SatisfiesFormula rho left -> SatisfiesFormula rho right
  | Formula.neg body =>
      Not (SatisfiesFormula rho body)
  | Formula.forallVar s n body =>
      forall value : M.Carrier s,
        SatisfiesFormula (updateAssignment rho s n value) body
  | Formula.existsVar s n body =>
      exists value : M.Carrier s,
        SatisfiesFormula (updateAssignment rho s n value) body

def SatisfiesAll {M : SigmaModel} (rho : Assignment M) :
    List Formula -> Prop
  | [] => True
  | formula :: rest =>
      And (SatisfiesFormula rho formula) (SatisfiesAll rho rest)

def SemanticallyEntails (premises : List Formula) (conclusion : Formula) :
    Prop :=
  forall (M : SigmaModel) (rho : Assignment M),
    SatisfiesAll rho premises -> SatisfiesFormula rho conclusion

structure SemanticCountermodel
    (premises : List Formula) (conclusion : Formula) : Type 1 where
  M : SigmaModel
  rho : Assignment M
  premisesTrue : SatisfiesAll rho premises
  conclusionFalse : Not (SatisfiesFormula rho conclusion)

def UsesSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput) : Prop :=
  M.interpPredicate PredicateSymbol.uses
    (Args.cons i (Args.cons o Args.nil))

def ClaimsSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (c : M.Carrier SortTag.claim) : Prop :=
  M.interpPredicate PredicateSymbol.claims
    (Args.cons i (Args.cons o (Args.cons c Args.nil)))

def SupportDegradedSem {M : SigmaModel}
    (e : M.Carrier SortTag.evidenceSet)
    (ctx : M.Carrier SortTag.context)
    (c : M.Carrier SortTag.claim) : Prop :=
  M.interpPredicate PredicateSymbol.supportDegraded
    (Args.cons e (Args.cons ctx (Args.cons c Args.nil)))

def TreatsAsAdequateSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (c : M.Carrier SortTag.claim)
    (ctx : M.Carrier SortTag.context) : Prop :=
  M.interpPredicate PredicateSymbol.treatsAsAdequate
    (Args.cons i (Args.cons o (Args.cons c (Args.cons ctx Args.nil))))

structure ISFSem (M : SigmaModel)
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (c : M.Carrier SortTag.claim)
    (e : M.Carrier SortTag.evidenceSet)
    (ctx : M.Carrier SortTag.context) : Prop where
  uses : UsesSem i o
  claims : ClaimsSem i o c
  supportDegraded : SupportDegradedSem e ctx c
  treatsAsAdequate : TreatsAsAdequateSem i o c ctx

def PowerRelevantSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (g : M.Carrier SortTag.affectedGroup) : Prop :=
  M.interpPredicate PredicateSymbol.powerRelevant
    (Args.cons i (Args.cons g Args.nil))

def PowerValidityDependenceSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (p : M.Carrier SortTag.powerCondition) : Prop :=
  M.interpPredicate PredicateSymbol.powerValidityDependence
    (Args.cons i (Args.cons o (Args.cons p Args.nil)))

def PowerOmittedSem {M : SigmaModel}
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (p : M.Carrier SortTag.powerCondition) : Prop :=
  M.interpPredicate PredicateSymbol.powerOmitted
    (Args.cons i (Args.cons o (Args.cons p Args.nil)))

structure M8Sem (M : SigmaModel)
    (i : M.Carrier SortTag.institution)
    (o : M.Carrier SortTag.symbolicOutput)
    (c : M.Carrier SortTag.claim)
    (e : M.Carrier SortTag.evidenceSet)
    (ctx : M.Carrier SortTag.context)
    (p : M.Carrier SortTag.powerCondition)
    (g : M.Carrier SortTag.affectedGroup) : Prop where
  uses : UsesSem i o
  claims : ClaimsSem i o c
  powerRelevant : PowerRelevantSem i g
  powerValidityDependence : PowerValidityDependenceSem i o p
  powerOmitted : PowerOmittedSem i o p
  supportDegraded : SupportDegradedSem e ctx c
  treatsAsAdequate : TreatsAsAdequateSem i o c ctx

theorem M8Sem_to_ISFSem {M : SigmaModel}
    {i : M.Carrier SortTag.institution}
    {o : M.Carrier SortTag.symbolicOutput}
    {c : M.Carrier SortTag.claim}
    {e : M.Carrier SortTag.evidenceSet}
    {ctx : M.Carrier SortTag.context}
    {p : M.Carrier SortTag.powerCondition}
    {g : M.Carrier SortTag.affectedGroup}
    (h : M8Sem M i o c e ctx p g) : ISFSem M i o c e ctx :=
  { uses := h.uses
    claims := h.claims
    supportDegraded := h.supportDegraded
    treatsAsAdequate := h.treatsAsAdequate }

def CandidateInsightSem {M : SigmaModel}
    (x : M.Carrier SortTag.candidateInsight) : Prop :=
  M.interpPredicate PredicateSymbol.candidateInsight
    (Args.cons x Args.nil)

def EvaluatorAcceptsSem {M : SigmaModel}
    (ev : M.Carrier SortTag.evaluator)
    (x : M.Carrier SortTag.candidateInsight) : Prop :=
  M.interpPredicate PredicateSymbol.evaluatorAccepts
    (Args.cons ev (Args.cons x Args.nil))

def LicensedTransitionSem {M : SigmaModel}
    (x : M.Carrier SortTag.candidateInsight)
    (source target : M.Carrier SortTag.frame) : Prop :=
  M.interpPredicate PredicateSymbol.licensedTransition
    (Args.cons x (Args.cons source (Args.cons target Args.nil)))

def NonTrivialTransformationSem {M : SigmaModel}
    (x : M.Carrier SortTag.candidateInsight)
    (source target : M.Carrier SortTag.frame) : Prop :=
  M.interpPredicate PredicateSymbol.nonTrivialTransformation
    (Args.cons x (Args.cons source (Args.cons target Args.nil)))

def ContradictionAddressedSem {M : SigmaModel}
    (x : M.Carrier SortTag.candidateInsight)
    (c : M.Carrier SortTag.claim) : Prop :=
  M.interpPredicate PredicateSymbol.contradictionAddressed
    (Args.cons x (Args.cons c Args.nil))

def NoHigherOrderDefeaterSem {M : SigmaModel}
    (ev : M.Carrier SortTag.evaluator)
    (x : M.Carrier SortTag.candidateInsight) : Prop :=
  M.interpPredicate PredicateSymbol.noHigherOrderDefeater
    (Args.cons ev (Args.cons x Args.nil))

def GenerativityMinimalSem {M : SigmaModel}
    (x : M.Carrier SortTag.candidateInsight) : Prop :=
  M.interpPredicate PredicateSymbol.generativityMinimal
    (Args.cons x Args.nil)

def DirectionalNonEquivalenceSem {M : SigmaModel}
    (source target : M.Carrier SortTag.frame) : Prop :=
  M.interpPredicate PredicateSymbol.directionalNonEquivalence
    (Args.cons source (Args.cons target Args.nil))

structure ValidInsightSem (M : SigmaModel)
    (x : M.Carrier SortTag.candidateInsight)
    (ev : M.Carrier SortTag.evaluator)
    (source target : M.Carrier SortTag.frame)
    (c : M.Carrier SortTag.claim) : Prop where
  candidateInsight : CandidateInsightSem x
  evaluatorAccepts : EvaluatorAcceptsSem ev x
  licensedTransition : LicensedTransitionSem x source target
  nonTrivialTransformation : NonTrivialTransformationSem x source target
  contradictionAddressed : ContradictionAddressedSem x c
  noHigherOrderDefeater : NoHigherOrderDefeaterSem ev x
  generativityMinimal : GenerativityMinimalSem x
  directionalNonEquivalence : DirectionalNonEquivalenceSem source target

theorem ValidInsightSem_to_EvaluatorAccepts {M : SigmaModel}
    {x : M.Carrier SortTag.candidateInsight}
    {ev : M.Carrier SortTag.evaluator}
    {source target : M.Carrier SortTag.frame}
    {c : M.Carrier SortTag.claim}
    (h : ValidInsightSem M x ev source target c) :
    EvaluatorAcceptsSem ev x :=
  h.evaluatorAccepts

def HarmBridgeSem {M : SigmaModel}
    (b : M.Carrier SortTag.normativeBridge)
    (i : M.Carrier SortTag.institution)
    (g : M.Carrier SortTag.affectedGroup) : Prop :=
  M.interpPredicate PredicateSymbol.harmBridge
    (Args.cons b (Args.cons i (Args.cons g Args.nil)))

def MoralGuiltBridgeSem {M : SigmaModel}
    (b : M.Carrier SortTag.normativeBridge)
    (i : M.Carrier SortTag.institution) : Prop :=
  M.interpPredicate PredicateSymbol.moralGuiltBridge
    (Args.cons b (Args.cons i Args.nil))

def RepairObligationBridgeSem {M : SigmaModel}
    (b : M.Carrier SortTag.normativeBridge)
    (i : M.Carrier SortTag.institution)
    (g : M.Carrier SortTag.affectedGroup) : Prop :=
  M.interpPredicate PredicateSymbol.repairObligationBridge
    (Args.cons b (Args.cons i (Args.cons g Args.nil)))

def EmpiricalValidationSem {M : SigmaModel}
    (v : M.Carrier SortTag.empiricalValidationObject)
    (c : M.Carrier SortTag.claim) : Prop :=
  M.interpPredicate PredicateSymbol.empiricalValidation
    (Args.cons v (Args.cons c Args.nil))

def ConstructValidSem {M : SigmaModel}
    (v : M.Carrier SortTag.empiricalValidationObject) : Prop :=
  M.interpPredicate PredicateSymbol.constructValid
    (Args.cons v Args.nil)

structure FullEmpiricalValidationSem (M : SigmaModel)
    (v : M.Carrier SortTag.empiricalValidationObject)
    (c : M.Carrier SortTag.claim) : Prop where
  validation : EmpiricalValidationSem v c
  constructValid : ConstructValidSem v
  reliabilityTested :
    M.interpPredicate PredicateSymbol.reliabilityTested
      (Args.cons v Args.nil)
  externallyReplicated :
    M.interpPredicate PredicateSymbol.externallyReplicated
      (Args.cons v Args.nil)

def UnitCarrier (_ : SortTag) : Type := Unit

def unitFunctionInterp (f : FunctionSymbol)
    (_args : Args UnitCarrier ((functionArity f).domain)) :
    UnitCarrier ((functionArity f).codomain) :=
  Unit.unit

def UnitPredicateModel (truth : PredicateSymbol -> Prop) : SigmaModel :=
  { Carrier := UnitCarrier
    interpFunction := unitFunctionInterp
    interpPredicate := fun p _args => truth p }

def m8OnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.uses => True
  | PredicateSymbol.claims => True
  | PredicateSymbol.supportDegraded => True
  | PredicateSymbol.treatsAsAdequate => True
  | PredicateSymbol.powerRelevant => True
  | PredicateSymbol.powerValidityDependence => True
  | PredicateSymbol.powerOmitted => True
  | _ => False

def m8OnlyModel : SigmaModel := UnitPredicateModel m8OnlyTruth

theorem m8Only_is_M8Sem :
    M8Sem m8OnlyModel Unit.unit Unit.unit Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  { uses := True.intro
    claims := True.intro
    powerRelevant := True.intro
    powerValidityDependence := True.intro
    powerOmitted := True.intro
    supportDegraded := True.intro
    treatsAsAdequate := True.intro }

theorem m8Only_not_harmBridge :
    Not (HarmBridgeSem (M := m8OnlyModel) Unit.unit Unit.unit Unit.unit) := by
  intro h
  exact h

theorem m8Only_not_moralGuiltBridge :
    Not (MoralGuiltBridgeSem (M := m8OnlyModel) Unit.unit Unit.unit) := by
  intro h
  exact h

theorem m8Only_not_repairObligationBridge :
    Not (RepairObligationBridgeSem (M := m8OnlyModel) Unit.unit Unit.unit
      Unit.unit) := by
  intro h
  exact h

def evaluatorOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.evaluatorAccepts => True
  | _ => False

def evaluatorOnlyModel : SigmaModel := UnitPredicateModel evaluatorOnlyTruth

theorem evaluatorOnly_accepts_sem :
    EvaluatorAcceptsSem (M := evaluatorOnlyModel) Unit.unit Unit.unit :=
  True.intro

theorem evaluatorOnly_not_ValidInsightSem :
    Not (ValidInsightSem evaluatorOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

def validInsightOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.candidateInsight => True
  | PredicateSymbol.evaluatorAccepts => True
  | PredicateSymbol.licensedTransition => True
  | PredicateSymbol.nonTrivialTransformation => True
  | PredicateSymbol.contradictionAddressed => True
  | PredicateSymbol.noHigherOrderDefeater => True
  | PredicateSymbol.generativityMinimal => True
  | PredicateSymbol.directionalNonEquivalence => True
  | _ => False

def validInsightOnlyModel : SigmaModel :=
  UnitPredicateModel validInsightOnlyTruth

theorem validInsightOnly_is_ValidInsightSem :
    ValidInsightSem validInsightOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit :=
  { candidateInsight := True.intro
    evaluatorAccepts := True.intro
    licensedTransition := True.intro
    nonTrivialTransformation := True.intro
    contradictionAddressed := True.intro
    noHigherOrderDefeater := True.intro
    generativityMinimal := True.intro
    directionalNonEquivalence := True.intro }

theorem validInsightOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem validInsightOnlyModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

def empiricalNominalTruth : PredicateSymbol -> Prop
  | PredicateSymbol.empiricalValidation => True
  | _ => False

def empiricalNominalModel : SigmaModel :=
  UnitPredicateModel empiricalNominalTruth

theorem empiricalNominal_has_EmpiricalValidationSem :
    EmpiricalValidationSem (M := empiricalNominalModel) Unit.unit Unit.unit :=
  True.intro

theorem empiricalNominal_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem empiricalNominalModel Unit.unit Unit.unit) := by
  intro h
  exact h.constructValid

end Paralogic
