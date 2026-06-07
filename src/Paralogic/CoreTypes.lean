/-!
Typed vocabulary for the Paralogic / ISFT core.

The first kernel is intentionally small. It provides typed placeholders for
frames, contexts, evaluators, claims, and bridge domains without pretending
that every later module is complete.
-/

namespace Paralogic

inductive SortTag where
  | institution
  | symbolicOutput
  | claim
  | evidenceSet
  | context
  | time
  | frame
  | evaluator
  | candidateInsight
  | powerCondition
  | affectedGroup
  | normativeBridge
  | empiricalValidationObject
  deriving DecidableEq, Repr

inductive ContradictionKind where
  | logical
  | semantic
  | pragmatic
  | normative
  | institutional
  | frameConflict
  | supportTreatment
  | symbolic
  | sacred
  | residue
  deriving DecidableEq, Repr

inductive DeltaOutcome where
  | resolution
  | shift
  | collapse
  | iterative
  | null
  | falseInsight
  | degenerate
  deriving DecidableEq, Repr

inductive FailureKind where
  | falseResolution
  | frameIncoherence
  | contradictionCollapse
  | symbolicDegeneration
  | insightSaturation
  | overgeneralization
  | recursiveBurnout
  | scopeFailure
  | evaluatorFailure
  | degenerateOutput
  | unrecoverableNull
  deriving DecidableEq, Repr

structure Frame where
  id : Nat
  scope : Nat
  deriving DecidableEq, Repr

structure Context where
  id : Nat
  policy : Nat
  deriving DecidableEq, Repr

structure Evaluator where
  id : Nat
  criteria : Nat
  deriving DecidableEq, Repr

structure TypedObject where
  sort : SortTag
  id : Nat
  deriving DecidableEq, Repr

structure Signature where
  sortCount : Nat
  functionSymbolCount : Nat
  predicateSymbolCount : Nat
  deriving DecidableEq, Repr

def SigmaParalogicCore : Signature :=
  { sortCount := 13, functionSymbolCount := 7, predicateSymbolCount := 32 }

theorem sigma_core_has_sorts : SigmaParalogicCore.sortCount = 13 := rfl

end Paralogic
