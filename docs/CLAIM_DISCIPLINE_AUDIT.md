# Claim Discipline Audit

## Purpose

This audit checks whether public-facing documents make claims stronger than
the repository currently supports.

## Scan Method

Inspected files:

- `README.md`
- `docs/CURRENT_STATUS.md`
- `docs/FULL_SYSTEM_AUDIT_2026-06-08.md`
- `docs/ENTIRE_SYSTEM_COMPLETION_PIPELINE.md`
- new benchmark documents

Search terms included complete, validated, proven useful, institution-ready,
commercial, compliance, wrongdoing, illegality, moral guilt, discrimination,
coercion, harm, governance illegitimacy, NIST, ISO, and EU AI Act.

## Forbidden Language List

Forbidden public claims include: complete system, empirically validated,
peer-reviewed, proven useful, institution-ready, compliance-ready, proves
wrongdoing, proves harm, proves illegality, proves moral guilt, proves
discrimination, or proves governance illegitimacy.

## Allowed Language List

Allowed public claims include: Lean-checked selected fragments, bounded
executable checks, scoped countermodels, operational schemas, incomplete,
protocol-only empirical status, and claim-boundary discipline.

## Files Inspected

The inspected files contain many risk words, but most occur in caveats,
forbidden-claim lists, historical audit notes, or explicit open-gap sections.

## Overclaim Findings

| finding | severity | response |
| --- | --- | --- |
| README lacked exact benchmark claim. | HIGH | Repaired in README update. |
| Current status lacked benchmark package links. | MEDIUM | Repaired in status update. |
| Pipeline title still says complete system. | MEDIUM | Treated as global historical roadmap; README/status clarify benchmark. |
| Operational completeness wording could be overread. | MEDIUM | Warrant ledger and claim page distinguish operational from empirical/source status. |

## Repaired Statements

- Public claim sentence added to README and public claim page.
- Benchmark links added to README and current status.
- Practical usefulness limited to claim-boundary discipline.

## Historical Documents That Remain Historical

Older audit and pipeline documents remain useful as historical snapshots. They
should be read through `docs/CURRENT_STATUS.md` and this benchmark package.

## Canonical Documents

- `README.md`
- `docs/CURRENT_STATUS.md`
- `docs/MATHEMATICAL_SERIOUSNESS_CLAIM.md`
- `docs/FORMAL_WORKBENCH_REVIEW_PACKET.md`
- `docs/REPRODUCIBILITY.md`

## Remaining Risks

The word "complete" appears in historical and open-gap contexts. A checker
should warn, not blindly fail, because negated uses are often correct.

Final checker result: `python python/claim_discipline_check.py` reports
`CDC-pass` with zero warnings after context-aware suppression for forbidden
claim lists and open-gap lists.

## Usefulness Check

This audit helps public readers and reviewers avoid inflated citation language.

## Claim Boundary

This audit does not prove absence of all overclaiming. It records a benchmark
claim-discipline pass over the current public entry points.
