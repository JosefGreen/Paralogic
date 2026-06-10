# Empirical Coding Manual

Status: EMP0 protocol artifact. No data has been collected or validated.

## Unit Of Analysis

One coded case is a pairing of:

- an institution;
- a symbolic output;
- a claim attributed to that output;
- an evidence/context packet used to assess the claim.

## Core Codes

Each code must be assigned as `yes`, `no`, `uncertain`, or `not_applicable`.
Every non-`not_applicable` code requires a short rationale and source span.

| Code | Question |
| --- | --- |
| uses | Does the institution use the symbolic output? |
| claims | Does the institution make or rely on the target claim through the output? |
| support_degraded | Is the support for the claim degraded in the declared context? |
| treats_as_adequate | Does the institution treat the degraded support as adequate? |
| power_relevant | Is a power condition relevant to claim validity? |
| power_validity_dependence | Does validity depend on the power condition? |
| power_omitted | Is the power condition omitted from the representation? |
| candidate_insight | Is a proposed insight identifiable? |
| evaluator_accepts | Does a declared evaluator accept the candidate insight? |
| licensed_transition | Does the insight license a source-to-target frame transition? |
| contradiction_addressed | Does the insight address the target contradiction? |
| no_higher_order_defeater | Are known higher-order defeaters absent? |

## Adjudication

Disagreements are resolved by an adjudicator who records:

- original coder labels;
- adjudicated label;
- reason for adjudication;
- whether the coding rule needs revision.

## Prohibited Coding Moves

- Do not code harm, guilt, illegality, or repair from ISF or M8 alone.
- Do not code empirical truth from ValidInsight alone.
- Do not code validation from formal consistency alone.
