# Candidate Mechanism Synthesis - 2026-06-11

Status: candidate-synthesized formal scaffold.

This document records a deliberate pipeline shift.  Missing M1-M12 mechanism
definitions should now be developed through a checked candidate tier before
they are promoted to source-backed or empirically validated semantics.

## Anti-Reward-Hacking Rule

A candidate mechanism definition is not a completed mechanism semantics.  It
must remain below source-backed status until the project records enough
source material to justify the mechanism-specific conditions, and below
empirical status until coded data, reliability checks, and validation exist.

Lean support: `src/Paralogic/MechanismSynthesis.lean`.

## Academic Lenses

The current candidate mapping uses the mechanism names from
`docs/SOURCE_RESOURCE_AUDIT_2026-06-08.md` and pairs each mechanism with a
disciplinary lens:

| Mechanism | Candidate lens | Candidate failure axis |
| --- | --- | --- |
| M1 Evidence Overclaim | evidential adequacy / Toulmin-style claim-support warranting | evidence-scope mismatch |
| M2 Metric-as-Value Collapse | Goodhart/Campbell metric-proxy critique | proxy-goal collapse |
| M3 Formal Access Substitution | access/substitution analysis | formal-access mismatch |
| M4 Symbolic Substitution | symbolic power and representation theory | symbolic-representation mismatch |
| M5 Repair Failure | staged repair and revision theory | repair-closure failure |
| M6 Translation Failure | actor-network / translation-network analysis | translation loss |
| M7 Category Essentialization | concept lattices and psychological/social essentialism | category-intent overreach |
| M8 Power Erasure | power-condition omission | power-condition omission |
| M9 Veto Suppression | participation and governance-veto analysis | participation suppression |
| M10 Frame Drift | Goffman/framing analysis | context-frame drift |
| M11 Symbolic Overload | symbolic load / interpretive overload analysis | symbol-interpretation overload |
| M12 Legitimacy Claim Decay | legitimacy and institutional theory | legitimacy overextension |

## External Pointers Used For Lens Selection

- Goodhart/Campbell metric-proxy critique: Goodhart's law and Campbell's law
  motivate M2 as a proxy-target collapse risk.
  Sources: [Goodhart's law](https://en.wikipedia.org/wiki/Goodhart%27s_law),
  [Campbell's law](https://en.wikipedia.org/wiki/Campbell%27s_law).
- Toulmin-style argument structure supports M1 as a claim/evidence/warrant
  adequacy problem.
  Source: [Toulmin model](https://en.wikipedia.org/wiki/Toulmin_model_of_argumentation).
- Symbolic power motivates M4 and helps keep symbolic diagnosis separate from
  legal, moral, or empirical conclusions.
  Source: [symbolic power](https://en.wikipedia.org/wiki/Symbolic_power).
- Actor-network translation and obligatory passage points motivate M6 as a
  translation-loss problem.
  Sources: [actor-network theory](https://en.wikipedia.org/wiki/Actor%E2%80%93network_theory),
  [obligatory passage point](https://en.wikipedia.org/wiki/Obligatory_passage_point).
- Framing analysis motivates M10 as context/frame drift rather than generic
  contradiction.
  Source: [frame analysis](https://en.wikipedia.org/wiki/Frame_analysis).
- Essentialism motivates M7 as category-intent overreach.
  Source: [essentialism](https://en.wikipedia.org/wiki/Essentialism).
- Suchman's legitimacy framework motivates M12 as legitimacy overextension or
  decay.
  Source: [Mark C. Suchman](https://en.wikipedia.org/wiki/Mark_C._Suchman).

These are starting lenses, not final literature review.  Publication-ready
use requires primary-source verification and external review.

## Lean Artifacts Added

- `MechanismSemanticMaturity`
- `MechanismLens`
- `mechanismLens`
- `CandidateFailureAxis`
- `mechanismFailureAxis`
- `CandidateMechanismDefinition`
- `CandidateMechanismDefinitionSatisfied`
- `CandidateMechanismDefinitionBlocked`
- `CandidateMechanismDefinition.toMechanismProfile`
- `candidate_satisfied_to_mechanism_profile_satisfied`
- `candidate_synthesized_not_source_backed`
- `candidate_synthesized_not_empirically_validated`
- `allISFTMechanisms`
- `allISFTMechanisms_length`
- `allISFTMechanisms_covers`
- `allISFTMechanisms_no_duplicates`
- `CandidateMechanismMappingCertified`
- `unit_candidate_mapping_certified`
- `CandidateMechanismSurfaceCertified`
- `unit_candidate_surface_certified`
- `CandidateMechanismCoverageComplete`
- `candidate_mechanism_coverage_complete`

## Coverage Gate

The candidate layer now has a dedicated coverage gate:

- Lean proves every M1-M12 mechanism is listed, uniquely covered, positively
  indexed, bounded by 12, and mapped into a satisfied candidate surface.
- `python/mechanism_coverage_check.py` independently parses the source and
  persists the result in `docs/mechanism_coverage_checks/`.
- `docs/MECHANISM_COVERAGE_CHECK_REPORT_2026-06-11.md` records the audit
  boundary: this is candidate coverage, not external validation.

## First Mechanism-Specific Deepening

M1 now has a dedicated formal module, `src/Paralogic/EvidenceOverclaim.lean`.
It models evidence overclaim through seven conditions: declared claim scope,
evidence relevance, evidence insufficiency, scope mismatch, unbounded
uncertainty, material overclaim, and absent adequacy boundary.

The module proves positive projection to support degradation and ISF semantics
when all conditions are satisfied, and it includes one concrete blocked witness
for each missing condition.  `python/evidence_overclaim_check.py` persists the
coverage result in `docs/evidence_overclaim_checks/`.

M2 has the parallel formal module, `src/Paralogic/MetricProxy.lean`.
It models metric-as-value collapse through declared target, proxy use,
optimization pressure, proxy-target divergence, material replacement, absent
boundary guard, and absent evaluator separation.  Its checker persists results
in `docs/metric_proxy_checks/`.

M3 now has the parallel formal module,
`src/Paralogic/FormalAccessSubstitution.lean`.  It models formal-access
substitution through declared formal access, absent substantive access,
access-as-sufficient treatment, material usability and comprehension barriers,
absent remedy path, and absent boundary guard.  Its checker persists results
in `docs/formal_access_checks/`.

M4 now has the parallel formal module,
`src/Paralogic/SymbolicSubstitution.lean`.  It models symbolic substitution
through symbol declaration, symbol-as-substantive treatment, representation
mismatch, absent material condition, material audience uptake, absent
correction path, and absent boundary guard.  Its checker persists results in
`docs/symbolic_substitution_checks/`.

M5 now has the parallel formal module, `src/Paralogic/RepairFailure.lean`.
It models repair failure through repair need, responsible agent identification,
absent repair plan, failed repair action, absent verification, material
recurrence, and maintained closure claim.  Its checker persists results in
`docs/repair_failure_checks/`.

## Pipeline Consequence

Lane D should now proceed by filling each mechanism with:

1. a candidate formal trigger;
2. a failure contrast;
3. a non-collapse guard;
4. a source trace;
5. an empirical coding plan;
6. positive Lean projection theorems;
7. negative Lean countermodels;
8. promotion criteria from candidate to source-backed or empirical status.
