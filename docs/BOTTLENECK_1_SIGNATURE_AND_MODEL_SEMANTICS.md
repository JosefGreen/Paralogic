# Bottleneck 1: Unified Type Signature and Model Semantics

Status: baseline formalization, PS2/MC1 for the full signature; EFC/EFE/PYC
for the encoded finite fragment in `python/paralogic_isft_core.py`.

Objective: define a conservative many-sorted signature for the Paralogic /
ISFT core, with typed objects, functions, predicates, model class,
interpretation, satisfaction, non-collapse guards, and verification status.

## Signature: Sigma_Paralogic_Core

### Sorts

- `Institution`
- `SymbolicOutput`
- `Claim`
- `EvidenceSet`
- `Context`
- `Time`
- `Frame`
- `FrameRule`
- `FrameHistory`
- `Contradiction`
- `Evaluator`
- `CandidateInsight`
- `ValidInsightObject`
- `DeltaOutcome`
- `FailureState`
- `PowerCondition`
- `AffectedGroup`
- `NormativeBridge`
- `EmpiricalValidationObject`
- `RepairAction`
- `AuditTrace`

### Function Symbols

- `EvBasis : SymbolicOutput x Claim x Context x Time -> EvidenceSet`
- `FrameOf : SymbolicOutput x Context -> Frame`
- `ContextOf : Frame -> Context`
- `EvalPayload : Evaluator x CandidateInsight x Context -> EvidenceSet`
- `DeltaClass : Frame x CandidateInsight x Context -> DeltaOutcome`
- `FailureClass : Frame x Context -> FailureState`
- `PowerBasis : Institution x SymbolicOutput x Claim x Context x Time ->
  PowerCondition`

### Predicate Symbols

ISFT kernel:

- `Uses(I,s,K,t)`
- `Claims(I,s,p,K,t)`
- `Adeq(E,p,K,t)`
- `SupportDegraded(s,p,K,t)`
- `TreatsAsAdequate(I,s,p,K,t)`
- `ISF(I,s,p,K,t)`

M8 power erasure:

- `PowerRelevant(P,p,Ag,K,t)`
- `PowerValidityDependence(p,P,K,t)`
- `PowerOmitted(I,P,s,p,K,t)`
- `M8(I,s,p,P,Ag,K,t)`

Insight and evaluator:

- `CandidateInsight(c)`
- `EvaluatorAccepts(R,c,K)`
- `LicensedTransition(c,F,K)`
- `NonTrivialTransformation(c,F,K)`
- `ContradictionAddressed(c,F,K)`
- `NoHigherOrderDefeater(c,F,K)`
- `GenerativityMinimal(c,F,K)`
- `DirectionalNonEquivalence(c,F,K)`
- `ValidInsight(c,F,R,K)`

Boundary predicates:

- `EmpiricalTruth(p,K,t)`
- `MoralTruth(p,K,t)`
- `Repair(I,Ag,K,t)`
- `Harm(h,I,Ag,K,t)`
- `Illegality(I,K,t)`
- `MoralGuilt(I,K,t)`
- `RepairObligation(I,Ag,K,t)`
- `GovernanceLegitimacy(I,K,t)`
- `Accountability(I,K,t)`
- `EmpiricalValidation(v,K,t)`

## Definitional Predicates

`SupportDegraded(s,p,K,t)` iff `not Adeq(EvBasis(s,p,K,t),p,K,t)`, or a
declared module-specific support defect holds.

Minimal executable fragment:

`ISF(I,s,p,K,t)` iff:

- `Uses(I,s,K,t)`
- `Claims(I,s,p,K,t)`
- `SupportDegraded(s,p,K,t)`
- `TreatsAsAdequate(I,s,p,K,t)`

`M8(I,s,p,P,Ag,K,t)` iff:

- `Uses(I,s,K,t)`
- `Claims(I,s,p,K,t)`
- `PowerRelevant(P,p,Ag,K,t)`
- `PowerValidityDependence(p,P,K,t)`
- `PowerOmitted(I,P,s,p,K,t)`
- `SupportDegraded(s,p,K,t)`
- `TreatsAsAdequate(I,s,p,K,t)`

`ValidInsight(c,F,R,K)` iff:

- `CandidateInsight(c)`
- `EvaluatorAccepts(R,c,K)`
- `LicensedTransition(c,F,K)`
- `NonTrivialTransformation(c,F,K)`
- `ContradictionAddressed(c,F,K)`
- `NoHigherOrderDefeater(c,F,K)`
- `GenerativityMinimal(c,F,K)`
- `DirectionalNonEquivalence(c,F,K)`

## Model Class

A model `M` for the core signature assigns:

- a nonempty carrier set to every sort;
- a total interpretation to each function symbol;
- a relation interpretation to each predicate symbol;
- an interpretation of defined predicates that satisfies the definitional
  equivalences above.

For finite executable checking, the current Python module uses a one-object
Boolean abstraction: each primitive predicate is assigned true or false, and
defined predicates are computed by conjunction.

## Satisfaction Relation

For assignment `rho`:

- `M, rho |= P(a1,...,an)` iff the interpreted tuple is in `P^M`.
- `M, rho |= not phi` iff not `M, rho |= phi`.
- `M, rho |= phi and psi` iff both conjuncts are satisfied.
- `M, rho |= exists x:tau. phi` iff some element of `D_tau^M` satisfies
  `phi` under the updated assignment.
- `M, rho |= forall x:tau. phi` iff every element of `D_tau^M` satisfies
  `phi` under the updated assignment.

## Core Theorems

- `ISF -> Uses` [EFE/PYC for finite fragment].
- `ISF -> Claims` [EFE/PYC for finite fragment].
- `ISF -> SupportDegraded` [EFE/PYC for finite fragment].
- `ISF -> TreatsAsAdequate` [EFE/PYC for finite fragment].
- `M8 -> ISF` [EFE/PYC for finite fragment].
- `ValidInsight -> EvaluatorAccepts` [EFE/PYC for finite fragment].

## Protected Non-Entailments

- `Uses not-> ISF` [EFC].
- `Claims not-> ISF` [EFC].
- `SupportDegraded not-> ISF` [EFC].
- `Uses + Claims + SupportDegraded not-> ISF` [EFC].
- `ISF not-> M8` [EFC].
- `M8 not-> Harm` [EFC].
- `M8 not-> Illegality` [EFC].
- `M8 not-> MoralGuilt` [EFC].
- `M8 not-> RepairObligation` [EFC].
- `CandidateInsight not-> ValidInsight` [EFC].
- `EvaluatorAccepts not-> ValidInsight` [EFC].
- `ValidInsight not-> EmpiricalTruth` [EFC].
- `ValidInsight not-> MoralTruth` [EFC].
- `ValidInsight not-> Repair` [EFC].

## Non-Collapse Audit

Formal validity is not empirical truth. Formal failure is not moral guilt.
ISF is not illegality. M8 is not discrimination, coercion, harm, or repair
obligation. ValidInsight is not moral truth. Evaluator acceptance is not
empirical validation.

## Gap Update

- Full many-sorted model semantics need Lean or another proof assistant.
- The current executable checker covers only one-object Boolean fragments.
- Adeq remains an externally supplied/domain-coded predicate in real cases.
- Normative bridges are typed but not validated.
- Empirical validation remains EMP0.
