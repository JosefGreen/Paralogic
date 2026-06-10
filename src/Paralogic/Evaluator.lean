import Paralogic.ModelSemantics

/-!
Evaluator criteria and criteria-relative soundness.

Evaluator acceptance is not truth.  This module makes acceptance conditional on
declared criteria and gives a separate structure for criteria-relative
soundness.
-/

namespace Paralogic

inductive EvaluationValue where
  | accepts
  | rejects
  | abstains
  | error
  deriving DecidableEq, Repr

inductive EvaluationErrorKind where
  | missingCriteria
  | irrelevantCriteria
  | insufficientEvidence
  | conflictDetected
  | malformedPayload
  | scopeMismatch
  | timeout
  deriving DecidableEq, Repr

structure EvaluatorCriteria (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  criteriaDeclared : Prop
  criteriaRelevant : Prop
  evidenceInspected : Prop
  criteriaApplied : Prop
  noEvaluationError : Prop
  warrant :
    criteriaDeclared ->
    criteriaRelevant ->
    evidenceInspected ->
    criteriaApplied ->
    noEvaluationError ->
    EvaluatorAcceptsSem evaluator candidate

structure EvaluatorCriteriaSatisfied {M : SigmaModel}
    (criteria : EvaluatorCriteria M) : Prop where
  declared : criteria.criteriaDeclared
  relevant : criteria.criteriaRelevant
  inspected : criteria.evidenceInspected
  applied : criteria.criteriaApplied
  noError : criteria.noEvaluationError

theorem EvaluatorCriteria_to_accepts {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : EvaluatorCriteriaSatisfied criteria) :
    EvaluatorAcceptsSem criteria.evaluator criteria.candidate :=
  criteria.warrant h.declared h.relevant h.inspected h.applied h.noError

def EvaluatorCriteriaBlocked {M : SigmaModel}
    (criteria : EvaluatorCriteria M) : Prop :=
  Or (Not criteria.criteriaDeclared)
    (Or (Not criteria.criteriaRelevant)
      (Or (Not criteria.evidenceInspected)
        (Or (Not criteria.criteriaApplied) (Not criteria.noEvaluationError))))

theorem missing_criteria_declaration_blocks_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : Not criteria.criteriaDeclared) :
    EvaluatorCriteriaBlocked criteria :=
  Or.inl h

theorem irrelevant_criteria_blocks_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : Not criteria.criteriaRelevant) :
    EvaluatorCriteriaBlocked criteria :=
  Or.inr (Or.inl h)

theorem uninspected_evidence_blocks_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : Not criteria.evidenceInspected) :
    EvaluatorCriteriaBlocked criteria :=
  Or.inr (Or.inr (Or.inl h))

theorem unapplied_criteria_blocks_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : Not criteria.criteriaApplied) :
    EvaluatorCriteriaBlocked criteria :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem evaluation_error_blocks_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (h : Not criteria.noEvaluationError) :
    EvaluatorCriteriaBlocked criteria :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

structure CriteriaRelativeSoundness {M : SigmaModel}
    (criteria : EvaluatorCriteria M) where
  conclusion : Prop
  acceptsSupportsConclusion :
    EvaluatorAcceptsSem criteria.evaluator criteria.candidate -> conclusion

theorem criteria_relative_soundness_to_conclusion {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (soundness : CriteriaRelativeSoundness criteria)
    (h : EvaluatorCriteriaSatisfied criteria) :
    soundness.conclusion :=
  soundness.acceptsSupportsConclusion (EvaluatorCriteria_to_accepts criteria h)

structure EvaluatorRejection (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  reasonDeclared : Prop

structure EvaluatorAbstention (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  insufficiencyDeclared : Prop

def RejectionDoesNotMeanFalse {M : SigmaModel}
    (_rejection : EvaluatorRejection M) : Prop := True

def AbstentionDoesNotMeanFalse {M : SigmaModel}
    (_abstention : EvaluatorAbstention M) : Prop := True

theorem rejection_noncollapse {M : SigmaModel}
    (rejection : EvaluatorRejection M) :
    RejectionDoesNotMeanFalse rejection :=
  True.intro

theorem abstention_noncollapse {M : SigmaModel}
    (abstention : EvaluatorAbstention M) :
    AbstentionDoesNotMeanFalse abstention :=
  True.intro

def EvaluatorRejectionSatisfied {M : SigmaModel}
    (rejection : EvaluatorRejection M) : Prop :=
  rejection.reasonDeclared

def EvaluatorAbstentionSatisfied {M : SigmaModel}
    (abstention : EvaluatorAbstention M) : Prop :=
  abstention.insufficiencyDeclared

theorem evaluation_accepts_ne_rejects :
    Not (EvaluationValue.accepts = EvaluationValue.rejects) := by
  intro h
  cases h

theorem evaluation_accepts_ne_abstains :
    Not (EvaluationValue.accepts = EvaluationValue.abstains) := by
  intro h
  cases h

theorem evaluation_accepts_ne_error :
    Not (EvaluationValue.accepts = EvaluationValue.error) := by
  intro h
  cases h

structure EvaluatorDecisionCase (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  value : EvaluationValue
  criteriaDeclared : Prop
  evidenceInspected : Prop
  criteriaApplied : Prop
  scopeMatched : Prop
  noEvaluationError : Prop
  acceptsWarrant :
    value = EvaluationValue.accepts ->
    criteriaDeclared ->
    evidenceInspected ->
    criteriaApplied ->
    scopeMatched ->
    noEvaluationError ->
    EvaluatorAcceptsSem evaluator candidate

structure EvaluatorDecisionSatisfied {M : SigmaModel}
    (decision : EvaluatorDecisionCase M) : Prop where
  declared : decision.criteriaDeclared
  inspected : decision.evidenceInspected
  applied : decision.criteriaApplied
  inScope : decision.scopeMatched
  noError : decision.noEvaluationError

theorem accepting_decision_to_accepts {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (hvalue : decision.value = EvaluationValue.accepts)
    (h : EvaluatorDecisionSatisfied decision) :
    EvaluatorAcceptsSem decision.evaluator decision.candidate :=
  decision.acceptsWarrant hvalue h.declared h.inspected h.applied h.inScope
    h.noError

def EvaluatorDecisionBlocked {M : SigmaModel}
    (decision : EvaluatorDecisionCase M) : Prop :=
  Or (Not decision.criteriaDeclared)
    (Or (Not decision.evidenceInspected)
      (Or (Not decision.criteriaApplied)
        (Or (Not decision.scopeMatched) (Not decision.noEvaluationError))))

theorem decision_missing_criteria_blocks {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (h : Not decision.criteriaDeclared) :
    EvaluatorDecisionBlocked decision :=
  Or.inl h

theorem decision_uninspected_evidence_blocks {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (h : Not decision.evidenceInspected) :
    EvaluatorDecisionBlocked decision :=
  Or.inr (Or.inl h)

theorem decision_unapplied_criteria_blocks {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (h : Not decision.criteriaApplied) :
    EvaluatorDecisionBlocked decision :=
  Or.inr (Or.inr (Or.inl h))

theorem decision_scope_mismatch_blocks {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (h : Not decision.scopeMatched) :
    EvaluatorDecisionBlocked decision :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem decision_error_blocks {M : SigmaModel}
    (decision : EvaluatorDecisionCase M)
    (h : Not decision.noEvaluationError) :
    EvaluatorDecisionBlocked decision :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

structure EvaluatorErrorCase (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  kind : EvaluationErrorKind
  errorDetected : Prop
  errorClassified : Prop
  unresolved : Prop

def EvaluatorErrorCaseSatisfied {M : SigmaModel}
    (err : EvaluatorErrorCase M) : Prop :=
  And err.errorDetected (And err.errorClassified err.unresolved)

def EvaluatorErrorBlocksAcceptance {M : SigmaModel}
    (err : EvaluatorErrorCase M) : Prop :=
  EvaluatorErrorCaseSatisfied err

theorem detected_error_blocks_acceptance_warrant {M : SigmaModel}
    (err : EvaluatorErrorCase M)
    (h : EvaluatorErrorCaseSatisfied err) :
    EvaluatorErrorBlocksAcceptance err :=
  h

structure EvaluatorIncompleteCase (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  missingCriteria : Prop
  insufficientEvidence : Prop
  unresolvedConflict : Prop

def EvaluatorIncompleteCaseSatisfied {M : SigmaModel}
    (inc : EvaluatorIncompleteCase M) : Prop :=
  Or inc.missingCriteria (Or inc.insufficientEvidence inc.unresolvedConflict)

theorem missing_criteria_yields_incomplete_case {M : SigmaModel}
    (inc : EvaluatorIncompleteCase M)
    (h : inc.missingCriteria) :
    EvaluatorIncompleteCaseSatisfied inc :=
  Or.inl h

theorem insufficient_evidence_yields_incomplete_case {M : SigmaModel}
    (inc : EvaluatorIncompleteCase M)
    (h : inc.insufficientEvidence) :
    EvaluatorIncompleteCaseSatisfied inc :=
  Or.inr (Or.inl h)

theorem unresolved_conflict_yields_incomplete_case {M : SigmaModel}
    (inc : EvaluatorIncompleteCase M)
    (h : inc.unresolvedConflict) :
    EvaluatorIncompleteCaseSatisfied inc :=
  Or.inr (Or.inr h)

structure CriteriaCompletenessProfile (M : SigmaModel) where
  evaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  domainBounded : Prop
  criteriaTotalForDomain : Prop
  evidenceAvailable : Prop
  conflictResolved : Prop
  abstentionRuleDeclared : Prop
  errorRuleDeclared : Prop

structure CriteriaCompletenessSatisfied {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M) : Prop where
  bounded : profile.domainBounded
  total : profile.criteriaTotalForDomain
  available : profile.evidenceAvailable
  conflictFree : profile.conflictResolved
  abstentionRule : profile.abstentionRuleDeclared
  errorRule : profile.errorRuleDeclared

def CriteriaCompletenessBlocked {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M) : Prop :=
  Or (Not profile.domainBounded)
    (Or (Not profile.criteriaTotalForDomain)
      (Or (Not profile.evidenceAvailable)
        (Or (Not profile.conflictResolved)
          (Or (Not profile.abstentionRuleDeclared)
            (Not profile.errorRuleDeclared)))))

theorem unbounded_domain_blocks_criteria_completeness {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.domainBounded) :
    CriteriaCompletenessBlocked profile :=
  Or.inl h

theorem partial_criteria_blocks_criteria_completeness {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.criteriaTotalForDomain) :
    CriteriaCompletenessBlocked profile :=
  Or.inr (Or.inl h)

theorem unavailable_evidence_blocks_criteria_completeness {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.evidenceAvailable) :
    CriteriaCompletenessBlocked profile :=
  Or.inr (Or.inr (Or.inl h))

theorem unresolved_conflict_blocks_criteria_completeness {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.conflictResolved) :
    CriteriaCompletenessBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem missing_abstention_rule_blocks_criteria_completeness
    {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.abstentionRuleDeclared) :
    CriteriaCompletenessBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem missing_error_rule_blocks_criteria_completeness {M : SigmaModel}
    (profile : CriteriaCompletenessProfile M)
    (h : Not profile.errorRuleDeclared) :
    CriteriaCompletenessBlocked profile :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

structure CriteriaRelativeCompleteness {M : SigmaModel}
    (criteria : EvaluatorCriteria M) where
  domainConclusion : Prop
  conclusionTriggersCriteria :
    domainConclusion -> EvaluatorCriteriaSatisfied criteria

theorem criteria_relative_completeness_to_acceptance {M : SigmaModel}
    (criteria : EvaluatorCriteria M)
    (completeness : CriteriaRelativeCompleteness criteria)
    (h : completeness.domainConclusion) :
    EvaluatorAcceptsSem criteria.evaluator criteria.candidate :=
  EvaluatorCriteria_to_accepts criteria
    (completeness.conclusionTriggersCriteria h)

structure MetaEvaluatorCase (M : SigmaModel) where
  metaEvaluator : M.Carrier SortTag.evaluator
  primaryEvaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  primaryAccepts : EvaluatorAcceptsSem primaryEvaluator candidate
  metaEndorsesProcedure : Prop
  oversightCriteriaDeclared : Prop
  noMetaConflict : Prop

structure MetaEvaluatorSatisfied {M : SigmaModel}
    (caseData : MetaEvaluatorCase M) : Prop where
  procedure : caseData.metaEndorsesProcedure
  declared : caseData.oversightCriteriaDeclared
  conflictFree : caseData.noMetaConflict

theorem meta_evaluator_case_to_primary_accepts {M : SigmaModel}
    (caseData : MetaEvaluatorCase M) :
    EvaluatorAcceptsSem caseData.primaryEvaluator caseData.candidate :=
  caseData.primaryAccepts

structure EvaluatorChainCase (M : SigmaModel) where
  firstEvaluator : M.Carrier SortTag.evaluator
  secondEvaluator : M.Carrier SortTag.evaluator
  candidate : M.Carrier SortTag.candidateInsight
  context : M.Carrier SortTag.context
  firstAccepts : EvaluatorAcceptsSem firstEvaluator candidate
  secondAccepts : EvaluatorAcceptsSem secondEvaluator candidate
  chainLinked : Prop
  noKnownConflict : Prop

structure EvaluatorChainSatisfied {M : SigmaModel}
    (chain : EvaluatorChainCase M) : Prop where
  linked : chain.chainLinked
  conflictFree : chain.noKnownConflict

theorem evaluator_chain_to_first_accepts {M : SigmaModel}
    (chain : EvaluatorChainCase M) :
    EvaluatorAcceptsSem chain.firstEvaluator chain.candidate :=
  chain.firstAccepts

theorem evaluator_chain_to_second_accepts {M : SigmaModel}
    (chain : EvaluatorChainCase M) :
    EvaluatorAcceptsSem chain.secondEvaluator chain.candidate :=
  chain.secondAccepts

def chainOnlyTruth : PredicateSymbol -> Prop
  | PredicateSymbol.evaluatorAccepts => True
  | _ => False

def chainOnlyModel : SigmaModel := UnitPredicateModel chainOnlyTruth

def chainOnly_case : EvaluatorChainCase chainOnlyModel :=
  { firstEvaluator := Unit.unit
    secondEvaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    firstAccepts := True.intro
    secondAccepts := True.intro
    chainLinked := True
    noKnownConflict := True }

theorem chainOnly_satisfied :
    EvaluatorChainSatisfied chainOnly_case :=
  { linked := True.intro
    conflictFree := True.intro }

theorem chainOnly_not_ValidInsightSem :
    Not (ValidInsightSem chainOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem chainOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem chainOnlyModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

theorem evaluatorOnly_acceptance_not_full_empirical_validation :
    Not (FullEmpiricalValidationSem evaluatorOnlyModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

def completeCriteriaOnlyProfile :
    CriteriaCompletenessProfile evaluatorOnlyModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    domainBounded := True
    criteriaTotalForDomain := True
    evidenceAvailable := True
    conflictResolved := True
    abstentionRuleDeclared := True
    errorRuleDeclared := True }

theorem completeCriteriaOnlyProfile_satisfied :
    CriteriaCompletenessSatisfied completeCriteriaOnlyProfile :=
  { bounded := True.intro
    total := True.intro
    available := True.intro
    conflictFree := True.intro
    abstentionRule := True.intro
    errorRule := True.intro }

def metaEvaluatorOnly_case : MetaEvaluatorCase evaluatorOnlyModel :=
  { metaEvaluator := Unit.unit
    primaryEvaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    primaryAccepts := True.intro
    metaEndorsesProcedure := True
    oversightCriteriaDeclared := True
    noMetaConflict := True }

theorem metaEvaluatorOnly_satisfied :
    MetaEvaluatorSatisfied metaEvaluatorOnly_case :=
  { procedure := True.intro
    declared := True.intro
    conflictFree := True.intro }

theorem metaEvaluatorOnly_primary_accepts :
    EvaluatorAcceptsSem (M := evaluatorOnlyModel) Unit.unit Unit.unit :=
  meta_evaluator_case_to_primary_accepts metaEvaluatorOnly_case

theorem metaEvaluatorOnly_not_ValidInsightSem :
    Not (ValidInsightSem evaluatorOnlyModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem metaEvaluatorOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem evaluatorOnlyModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

def acceptingDecisionOnly : EvaluatorDecisionCase evaluatorOnlyModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    value := EvaluationValue.accepts
    criteriaDeclared := True
    evidenceInspected := True
    criteriaApplied := True
    scopeMatched := True
    noEvaluationError := True
    acceptsWarrant := fun _ _ _ _ _ _ => True.intro }

theorem acceptingDecisionOnly_satisfied :
    EvaluatorDecisionSatisfied acceptingDecisionOnly :=
  { declared := True.intro
    inspected := True.intro
    applied := True.intro
    inScope := True.intro
    noError := True.intro }

theorem acceptingDecisionOnly_accepts :
    EvaluatorAcceptsSem (M := evaluatorOnlyModel) Unit.unit Unit.unit :=
  accepting_decision_to_accepts acceptingDecisionOnly rfl
    acceptingDecisionOnly_satisfied

def noEvaluatorTruth (_p : PredicateSymbol) : Prop := False

def noEvaluatorModel : SigmaModel := UnitPredicateModel noEvaluatorTruth

def rejectionOnly_case : EvaluatorRejection noEvaluatorModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    reasonDeclared := True }

def abstentionOnly_case : EvaluatorAbstention noEvaluatorModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    insufficiencyDeclared := True }

theorem rejectionOnly_satisfied :
    EvaluatorRejectionSatisfied rejectionOnly_case :=
  True.intro

theorem abstentionOnly_satisfied :
    EvaluatorAbstentionSatisfied abstentionOnly_case :=
  True.intro

theorem rejectionOnly_not_ValidInsightSem :
    Not (ValidInsightSem noEvaluatorModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem abstentionOnly_not_ValidInsightSem :
    Not (ValidInsightSem noEvaluatorModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

def errorOnly_case : EvaluatorErrorCase noEvaluatorModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    kind := EvaluationErrorKind.malformedPayload
    errorDetected := True
    errorClassified := True
    unresolved := True }

theorem errorOnly_satisfied :
    EvaluatorErrorCaseSatisfied errorOnly_case :=
  And.intro True.intro (And.intro True.intro True.intro)

theorem errorOnly_not_ValidInsightSem :
    Not (ValidInsightSem noEvaluatorModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

def incompleteOnly_case : EvaluatorIncompleteCase noEvaluatorModel :=
  { evaluator := Unit.unit
    candidate := Unit.unit
    context := Unit.unit
    missingCriteria := True
    insufficientEvidence := False
    unresolvedConflict := False }

theorem incompleteOnly_satisfied :
    EvaluatorIncompleteCaseSatisfied incompleteOnly_case :=
  Or.inl True.intro

theorem incompleteOnly_not_ValidInsightSem :
    Not (ValidInsightSem noEvaluatorModel Unit.unit Unit.unit Unit.unit
      Unit.unit Unit.unit) := by
  intro h
  exact h.candidateInsight

theorem rejectionOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem noEvaluatorModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

theorem abstentionOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem noEvaluatorModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

theorem errorOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem noEvaluatorModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

theorem incompleteOnly_not_FullEmpiricalValidationSem :
    Not (FullEmpiricalValidationSem noEvaluatorModel Unit.unit Unit.unit) := by
  intro h
  exact h.validation

end Paralogic
