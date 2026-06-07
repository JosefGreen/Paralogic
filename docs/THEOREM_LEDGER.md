# Theorem Ledger

All listed entries are encoded in Lean unless marked as future work.

| ID | Statement | Lean artifact |
| --- | --- | --- |
| T-ISF-1 | `ISF -> Uses` | `ISF_to_Uses` |
| T-ISF-2 | `ISF -> Claims` | `ISF_to_Claims` |
| T-ISF-3 | `ISF -> SupportDegraded` | `ISF_to_SupportDegraded` |
| T-ISF-4 | `ISF -> TreatsAsAdequate` | `ISF_to_TreatsAsAdequate` |
| T-M8-1 | `M8 -> ISF` | `M8_to_ISF` |
| T-M8-2 | `M8 -> Uses` | `M8_to_Uses` |
| T-M8-3 | `M8 -> Claims` | `M8_to_Claims` |
| T-VI-1 | `ValidInsight -> CandidateInsight` | `ValidInsight_to_CandidateInsight` |
| T-VI-2 | `ValidInsight -> EvaluatorAccepts` | `ValidInsight_to_EvaluatorAccepts` |
| C-ISF-1 | `Uses not-> ISF` | `ISF_does_not_follow_from_Uses` |
| C-ISF-2 | `Claims not-> ISF` | `ISF_does_not_follow_from_Claims` |
| C-ISF-3 | `SupportDegraded not-> ISF` | `ISF_does_not_follow_from_SupportDegraded` |
| C-ISF-4 | `Uses + Claims + SupportDegraded not-> ISF` | `ISF_needs_TreatsAsAdequate` |
| C-M8-1 | `ISF not-> M8` | `ISF_does_not_imply_M8` |
| C-M8-2 | `M8 not-> Harm` | `M8_does_not_imply_harm` |
| C-M8-3 | `M8 not-> Illegality` | `M8_does_not_imply_illegality` |
| C-M8-4 | `M8 not-> MoralGuilt` | `M8_does_not_imply_moralGuilt` |
| C-EVAL-1 | `EvaluatorAccepts not-> ValidInsight` | `EvaluatorAccepts_does_not_imply_ValidInsight` |
| C-VI-1 | `ValidInsight not-> EmpiricalTruth` | `ValidInsight_does_not_imply_empiricalTruth` |
| C-VI-2 | `ValidInsight not-> Repair` | `ValidInsight_does_not_imply_repair` |
| C-DELTA-1 | `DeltaResolution not-> EmpiricalTruth` | `DeltaResolution_does_not_imply_empiricalTruth` |
| C-EMP-1 | `EmpiricalValidation not-> GovernanceLegitimacy` | `EmpiricalValidation_does_not_imply_governanceLegitimacy` |

## Future Theorem Families

- Many-sorted soundness for the finite kernel embedding.
- Frame morphism preservation and non-preservation theorems.
- Evaluator soundness relative to explicit criteria.
- Delta outcome exclusivity or overlap theorems.
- Repair calculus non-collapse theorems.
- Normative bridge soundness and non-entailment theorems.
- Empirical validation boundary theorems.
