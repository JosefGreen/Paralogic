# Theorem Ledger

This ledger records current theorem status for the repository, not for every
source document ever drafted.

## Executable Finite Fragment

| ID | Statement | Status |
| --- | --- | --- |
| EFE-ISF-01 | `ISF -> Uses` | EFE/PYC |
| EFE-ISF-02 | `ISF -> Claims` | EFE/PYC |
| EFE-ISF-03 | `ISF -> SupportDegraded` | EFE/PYC |
| EFE-ISF-04 | `ISF -> TreatsAsAdequate` | EFE/PYC |
| EFE-M8-01 | `M8 -> ISF` | EFE/PYC |
| EFE-EVAL-01 | `ValidInsight -> EvaluatorAccepts` | EFE/PYC |
| EFC-ISF-01 | `Uses not-> ISF` | EFC |
| EFC-ISF-02 | `Claims not-> ISF` | EFC |
| EFC-ISF-03 | `SupportDegraded not-> ISF` | EFC |
| EFC-ISF-04 | `Uses + Claims + SupportDegraded not-> ISF` | EFC |
| EFC-M8-01 | `ISF not-> M8` | EFC |
| EFC-M8-04 | `M8 not-> Discrimination` | EFC |
| EFC-M8-05 | `M8 not-> Coercion` | EFC |
| EFC-M8-06 | `M8 not-> Harm` | EFC |
| EFC-M8-07 | `M8 not-> Illegality` | EFC |
| EFC-M8-08 | `M8 not-> MoralGuilt` | EFC |
| EFC-M8-09 | `M8 not-> RepairObligation` | EFC |
| EFC-VI-01 | `CandidateInsight not-> ValidInsight` | EFC |
| EFC-VI-02 | `FrameShift not-> ValidInsight` | EFC |
| EFC-VI-03 | `ValidInsight not-> EmpiricalTruth` | EFC |
| EFC-VI-04 | `ValidInsight not-> MoralTruth` | EFC |
| EFC-VI-05 | `ValidInsight not-> Repair` | EFC |
| EFC-EVAL-02 | `EvaluatorAccepts not-> ValidInsight` | EFC |
| EFC-DELTA-01 | `DeltaResolution not-> EmpiricalTruth` | EFC |
| EFC-AUDIT-01 | `EmpiricalValidation not-> GovernanceLegitimacy` | EFC |
| EFC-AUDIT-02 | `Accountability not-> Repair` | EFC |

## Lean Candidate Layer

The Lean files under `src/Paralogic/` are candidate formalization material.
They are not currently promoted to MC3-Lean in this repository. A theorem may
enter this ledger as MC3-Lean only after a trusted Lean toolchain accepts it.

## Text-Level Theorem Families Needing Promotion

- Frame/context containment and projection non-collapse.
- Contradiction non-collapse.
- Evaluator acceptance non-collapse.
- Delta outcome non-finality.
- Recursion/failure taxonomy non-collapse.
- ISFT M1-M12 mechanism soundness and bounded completeness.
- Normative bridge boundary theorems.
- Empirical validation boundary theorems.

Each theorem family needs: typed statement, dependencies, proof status,
countermodel for non-entailments, machine-check status, and open issues.
