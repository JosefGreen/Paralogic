import Paralogic.ModelSemantics

/-!
Finite valuation models for executable checking.

This module gives a finite Boolean valuation framework for the many-sorted
signature.  It is a checker substrate, not yet a completed exhaustive checker
with stored witness output.
-/

namespace Paralogic

def allFunctionSymbols : List FunctionSymbol :=
  [ FunctionSymbol.outputInstitution,
    FunctionSymbol.outputContext,
    FunctionSymbol.claimEvidence,
    FunctionSymbol.claimContext,
    FunctionSymbol.evaluatorContext,
    FunctionSymbol.validationTarget,
    FunctionSymbol.bridgeTarget ]

def allPredicateSymbols : List PredicateSymbol :=
  [ PredicateSymbol.uses,
    PredicateSymbol.claims,
    PredicateSymbol.supports,
    PredicateSymbol.adequate,
    PredicateSymbol.supportDegraded,
    PredicateSymbol.treatsAsAdequate,
    PredicateSymbol.contradictionPresent,
    PredicateSymbol.contradictionAddressed,
    PredicateSymbol.candidateInsight,
    PredicateSymbol.evaluatorAccepts,
    PredicateSymbol.licensedTransition,
    PredicateSymbol.nonTrivialTransformation,
    PredicateSymbol.noHigherOrderDefeater,
    PredicateSymbol.generativityMinimal,
    PredicateSymbol.directionalNonEquivalence,
    PredicateSymbol.powerRelevant,
    PredicateSymbol.powerValidityDependence,
    PredicateSymbol.powerOmitted,
    PredicateSymbol.harmBridge,
    PredicateSymbol.responsibilityBridge,
    PredicateSymbol.repairObligationBridge,
    PredicateSymbol.accountabilityBridge,
    PredicateSymbol.legalIllegitimacyBridge,
    PredicateSymbol.governanceLegitimacyBridge,
    PredicateSymbol.moralGuiltBridge,
    PredicateSymbol.empiricalValidation,
    PredicateSymbol.constructValid,
    PredicateSymbol.reliabilityTested,
    PredicateSymbol.externallyReplicated ]

def PredicateValuation : Type :=
  PredicateSymbol -> Bool

def overwriteValuation (base : PredicateValuation)
    (symbol : PredicateSymbol) (value : Bool) : PredicateValuation :=
  fun p => if p = symbol then value else base p

def allPredicateValuationsFrom : List PredicateSymbol -> List PredicateValuation
  | [] => [fun _ => false]
  | symbol :: rest =>
      let tail := allPredicateValuationsFrom rest
      (List.map (fun v => overwriteValuation v symbol false) tail) ++
      (List.map (fun v => overwriteValuation v symbol true) tail)

def allPredicateValuations : List PredicateValuation :=
  allPredicateValuationsFrom allPredicateSymbols

theorem allFunctionSymbols_length :
    allFunctionSymbols.length = SigmaParalogicCore.functionSymbolCount := rfl

theorem allPredicateSymbols_length :
    allPredicateSymbols.length = SigmaParalogicCore.predicateSymbolCount := rfl

theorem allFunctionSymbols_complete (f : FunctionSymbol) :
    List.Mem f allFunctionSymbols := by
  cases f <;>
    repeat first
      | exact List.Mem.head _
      | apply List.Mem.tail

theorem allPredicateSymbols_complete (p : PredicateSymbol) :
    List.Mem p allPredicateSymbols := by
  cases p <;>
    repeat first
      | exact List.Mem.head _
      | apply List.Mem.tail

theorem allFunctionSymbols_nodup :
    allFunctionSymbols.Nodup := by
  decide

theorem allPredicateSymbols_nodup :
    allPredicateSymbols.Nodup := by
  decide

def finitePredicateModel (valuation : PredicateValuation) : SigmaModel :=
  UnitPredicateModel (fun p => valuation p = true)

def unitAssignment (M : SigmaModel)
    [forall s : SortTag, Inhabited (M.Carrier s)] : Assignment M :=
  fun _ _ => default

def unitModelAssignment : Assignment (finitePredicateModel (fun _ => false)) :=
  fun _ _ => Unit.unit

def FormulaHoldsInValuation (valuation : PredicateValuation)
    (formula : Formula) : Prop :=
  SatisfiesFormula (M := finitePredicateModel valuation)
    (fun _ _ => Unit.unit) formula

def CounterexampleValuation (premises : List Formula)
    (conclusion : Formula) (valuation : PredicateValuation) : Prop :=
  And (SatisfiesAll (M := finitePredicateModel valuation)
      (fun _ _ => Unit.unit) premises)
    (Not (SatisfiesFormula (M := finitePredicateModel valuation)
      (fun _ _ => Unit.unit) conclusion))

def SearchSpaceHasCounterexample (premises : List Formula)
    (conclusion : Formula) : Prop :=
  Exists (fun valuation =>
    And (List.Mem valuation allPredicateValuations)
      (CounterexampleValuation premises conclusion valuation))

structure FiniteSortWitness (M : SigmaModel) (s : SortTag) where
  elements : List (M.Carrier s)
  covers : forall x : M.Carrier s, List.Mem x elements

structure FiniteModelWitness (M : SigmaModel) where
  finiteCarrier : (s : SortTag) -> FiniteSortWitness M s

def HasFiniteModelWitness (M : SigmaModel) : Prop :=
  Exists (fun _witness : FiniteModelWitness M => True)

def NoFiniteWitnessRecorded (M : SigmaModel) : Prop :=
  Not (HasFiniteModelWitness M)

theorem no_finite_witness_is_not_infinitude_claim (M : SigmaModel) :
    NoFiniteWitnessRecorded M -> NoFiniteWitnessRecorded M := by
  intro h
  exact h

def unitFiniteSortWitness (s : SortTag) :
    FiniteSortWitness (UnitPredicateModel (fun _ => False)) s :=
  { elements := [Unit.unit]
    covers := by
      intro x
      cases x
      exact List.Mem.head [] }

def unitFiniteModelWitness :
    FiniteModelWitness (UnitPredicateModel (fun _ => False)) :=
  { finiteCarrier := unitFiniteSortWitness }

structure FiniteCheckTarget where
  id : String
  premises : List Formula
  conclusion : Formula
  expectsCounterexample : Bool

structure FiniteCheckCoverageRecord where
  target : FiniteCheckTarget
  searchedValuationCount : Nat
  witnessFound : Bool
  machineReadableWitnessRecorded : Bool

def CoverageRecordSatisfiesTarget
    (record : FiniteCheckCoverageRecord) : Prop :=
  And (record.witnessFound = record.target.expectsCounterexample)
    record.machineReadableWitnessRecorded

def CoverageRecordIncomplete
    (record : FiniteCheckCoverageRecord) : Prop :=
  Or (record.witnessFound ≠ record.target.expectsCounterexample)
    (Not record.machineReadableWitnessRecorded)

theorem missing_machine_witness_blocks_coverage
    (record : FiniteCheckCoverageRecord)
    (h : Not record.machineReadableWitnessRecorded) :
    CoverageRecordIncomplete record :=
  Or.inr h

theorem wrong_witness_expectation_blocks_coverage
    (record : FiniteCheckCoverageRecord)
    (h : record.witnessFound ≠ record.target.expectsCounterexample) :
    CoverageRecordIncomplete record :=
  Or.inl h

theorem coverage_record_satisfied_not_incomplete_by_witness_flag
    (record : FiniteCheckCoverageRecord)
    (h : CoverageRecordSatisfiesTarget record) :
    record.witnessFound = record.target.expectsCounterexample :=
  h.left

theorem finitePredicateModel_predicate_true
    (valuation : PredicateValuation) (p : PredicateSymbol)
    (args : Args (finitePredicateModel valuation).Carrier
      ((predicateArity p).domain))
    (h : valuation p = true) :
    (finitePredicateModel valuation).interpPredicate p args :=
  h

theorem finitePredicateModel_predicate_false
    (valuation : PredicateValuation) (p : PredicateSymbol)
    (args : Args (finitePredicateModel valuation).Carrier
      ((predicateArity p).domain))
    (h : valuation p = false) :
    Not ((finitePredicateModel valuation).interpPredicate p args) := by
  intro hp
  change valuation p = true at hp
  rw [h] at hp
  contradiction

end Paralogic
