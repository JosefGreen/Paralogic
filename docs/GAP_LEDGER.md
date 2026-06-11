# Gap Ledger

Canonical current audit: `docs/FULL_SYSTEM_AUDIT_2026-06-08.md`.

The project remains incomplete.  Entries below include historical progress
notes as well as open gaps.

## Immediate Gaps

1. The current `World` model is one-object and propositional.
2. There is no many-sorted first-order satisfaction relation yet.
3. `Adeq` is represented only by `supportDegraded`; domain adequacy is not
   operationalized.
4. M8 now has typed power dimensions, mitigation, disclosure, and
   affected-group conditions for the scoped fragment; it still has no concrete
   externally validated institutional case.
5. ValidInsight and evaluator criteria now have typed semantic and
   criteria-relative fragments; richer frame histories remain future work.
6. Delta outcomes are typed but not classified.
7. Failure taxonomy is typed but not semantically connected.
8. Normative bridges are not defined.
9. Empirical validation remains outside the formal kernel.
10. No external review has occurred.
11. There is no explicit carrier family for the complete `Sigma_Paralogic`.
12. Function symbols and predicate symbols are counted but not named,
    interpreted, or arity-checked.
13. Frame, context, contradiction, evaluator, normative bridge, and empirical
    validation semantics are placeholders rather than full model components.
14. There is no syntactic formula language separating derivability from
    semantic consequence.
15. There is now a bounded executable finite checker and machine-readable
    witness ledger for 10 scoped targets; there is still no global exhaustive
    finite model search over the complete many-sorted signature.
16. There is now a custom proof checker for a scoped Horn-like definitional
    implication fragment; broader proof-language coverage remains future work.
17. The current theorem families are mostly definitional projections and named
    witnesses; they are useful guards, not deep theory.
18. Gate 1 foundation lemmas have MC3 artifacts for the currently scoped
    fragment:
    identity substitution, satisfaction, semantic entailment, assignment
    agreement, binder non-freeness, quantifier-free substitution/satisfaction,
    free-variable agreement, closed-formula and closed-premise assignment
    invariance, and premise monotonicity. Broader quantified substitution
    theory remains a later extension, not a blocker for Gate 2.
19. Normative bridge schemas exist, but no domain-specific bridge has been
    justified by external legal, moral, institutional, or empirical standards.
20. The new many-sorted countermodel is a named witness, not an exhaustive
    finite model search.
21. Frame/context morphisms are present, but projection and translation laws
    are not yet developed.
21a. Model and frame/context morphism composition exist, and the old one-object
    kernel is embedded into the many-sorted semantics. Remaining Gate 2 work:
    preservation/non-preservation profiles and many-sorted countermodel
    families independent of the old kernel.
21b. Independent many-sorted countermodel families and a non-preservation
    witness now exist. Remaining Gate 2 work: finite/infinite model
    distinction and explicit coverage targets for executable checking.
21c. Finite model witness structures and coverage targets now exist. Gate 2 has
    MC3 artifacts for the currently scoped fragment; later extensions may strengthen
    finite enumeration algorithms and coverage proofs.
22. Preservation profiles are data records, not yet tied to partial morphism
    theorems.
23. Normative bridge schemas and several other modules include warrants as
    fields. `WarrantDischarge.lean` now enumerates the current warrant
    obligations and proves all are only countermodel-guarded, not yet
    source-backed or empirically validated. Adequacy now has a scoped
    operational discharge model with a negative control. Evaluator accepting
    decisions now have a scoped operational discharge model tied to high-score
    acceptance, also with a negative control. Remaining work: discharge each
    other obligation through operational rules, source-backed rules, empirical
    validation, or lower-level derivation.
24. Empirical validation protocols, measurement protocol, coding manual,
    dataset schema, reliability plan, construct-validity plan, pilot protocol,
    and replication plan now exist. No data, reliability statistic, validity
    study, or completed replication exists.
25. Finite valuation models, coverage target records, a bounded executable
    run, and stored witness files now exist for the scoped Gate 8 target set.
26. Adequacy profiles exist, but no domain-specific adequacy standard has been
    externally validated or tied to coding manuals.
27. Evaluator criteria, evaluator decisions, error cases, incomplete cases,
    criteria-completeness profiles, meta-evaluator cases, and evaluator-chain
    cases now exist with MC3-Lean checks for the scoped fragment.
28. M8 power-erasure condition schemas and M8 mechanism linkage exist, but no
    concrete externally validated institutional case, bridge dependency, or
    finite-search coverage artifact has been produced.
29. Gate 3 contradiction calculus has a typed contradiction case and first
    non-collapse witnesses, but contradiction kinds still need richer
    kind-specific semantics.
30. Contradiction profiles now have condition gates and blocker lemmas, but
    profile-to-case conversions and non-collapse witnesses need to be completed
    for every contradiction kind.
31. Gate 3 has MC3 artifacts for the scoped contradiction calculus fragment.
    Remaining
    future contradiction extensions include richer domain-specific semantics
    for each kind, but the pipeline now advances to Insight and Delta calculus.
31a. Warrant discharge now includes a scoped operational contradiction
    detector: active frame, active context, and contested claim imply
    contradiction presence, while resolved claim, inactive frame, and inactive
    context are negative controls.  Remaining contradiction work is
    kind-specific source grounding, richer domain semantics, and empirical
    coding/validation where empirical claims are made.
32. Gate 4 has initial insight and Delta outcome cases with non-collapse
    witnesses, but Delta exclusivity/overlap policy and all Delta outcome
    cases remain to be completed.
33. Delta policy and all basic Delta outcome cases now exist. Remaining Gate 4
    work: ValidInsight non-finality, transformability, and relation to
    contradiction-addressing.
34. Gate 4 has MC3 artifacts for the scoped Insight and Delta calculus fragment.
    Future extensions may add richer operational Delta classifiers, but the
    pipeline now advances to Evaluator Calculus.
35. Gate 5 has MC3 artifacts for the scoped evaluator calculus fragment and a
    finite evaluator-calibration layer with score levels, threshold decisions,
    disagreement witnesses, majority aggregation, and ECC-bounded executable
    checking over 27 score triples. Remaining future evaluator extensions
    include richer scoring rubrics, real evaluator datasets, reliability
    statistics, and external validation, but the pipeline now advances to the
    ISFT mechanism system.
35a. Warrant discharge now includes a scoped operational evaluator-criteria
    profile: declared, relevant, inspected, applied, and no-error criteria
    compute evaluator acceptance for an approved evaluator/candidate pair.
    Rejected candidates and low-score decisions remain negative controls.
    External evaluator standards, reliability statistics, and empirical
    calibration remain open.
36. Gate 6 has MC3 artifacts for the scoped ISFT mechanism fragment: M1-M12 labels,
    mechanism profiles, dependency-graph structure, bounded suite coverage,
    M8 power linkage, M12 boundary profile, and suppression algebra now have
    MC3-Lean artifacts. Richer domain semantics for M1-M7 and M9-M11 remain
    source-backed future extensions rather than inferred content.
36a. Gate 6 now has a candidate-synthesized mechanism semantics tier:
    `MechanismSynthesis.lean` maps every M1-M12 mechanism to an academic lens
    and candidate failure axis, gives candidate definitions explicit maturity
    status, and proves candidate-synthesized status is not source-backed or
    empirically validated. This is the new priority path for building missing
    definitions without pretending they are already externally grounded.
36b. M8 power-condition warrant discharge now has a scoped operational model
    for relevance, validity dependence, and omission, with negative controls
    for unaffected group, immaterial condition, and ordinary output.  Remaining
    power work is source-backed institutional semantics, external case
    grounding, and empirical coding where empirical claims are made.
36c. Suppression support-degradation warrant discharge now has a scoped
    operational model for supported evidence, matched context, and suppressed
    claim, with negative controls for unsupported evidence, mismatched context,
    and ordinary claim.  Remaining suppression work is richer mode-specific
    semantics and empirical coding where empirical claims are made.
37. Gate 7 has MC3 artifacts for the scoped adequacy, normative bridge, and repair
    fragment: seven normative bridge schema families, repair diagnosis, plan,
    action, verification, closure, regress, externality, bridge-defeater, and
    bridge-independence witnesses now have MC3-Lean artifacts. Concrete legal,
    moral, governance, and empirical standards still require external
    justification and are not claimed as validated.
37a. Repair-obligation warrant discharge now has a scoped operational model
    for repair-need bridge, responsible institution, and affected group, with
    negative controls for ordinary bridge, other institution, and other group.
    Remaining repair work is external legal, moral, governance, and empirical
    grounding where those claims are made.
38. Gate 8 has EFC artifacts for the scoped executable finite-checking fragment:
    `python/finite_check.py` produced EFC-bounded coverage and machine-readable
    witness artifacts for 10 target implications/non-entailments. This remains
    bounded target-relevant enumeration, not global exhaustive model search.
39. Gate 9 has PYC artifacts for the scoped custom proof-checker fragment:
    `python/proof_check.py` accepted supported Horn-like traces and rejected
    unsupported or premise-missing traces. This is PYC status only, not Lean
    verification or external review.
39a. Lane B proof theory now has a stronger MC3-Lean propositional derivability
    fragment with implication introduction, falsity elimination, disjunction
    elimination, right weakening, and PPC-bounded truth-table checks for seven
    positive/negative propositional targets. Scoped derivability rules and
    semantic laws now cover universal current-value elimination and
    existential current-value introduction, plus universal introduction under
    semantic premise-stability. Full syntactic no-free-variable freshness now
    discharges stability side conditions for universal introduction, including
    binder-shadowing cases. Direct semantic universal-introduction theorems now
    cover stability and no-free-variable freshness variants. A formal
    countermodel now shows unrestricted universal introduction from a premise
    with the generalized variable free is not semantically valid. Full
    quantified derivability with alpha-equivalence, eigenvariable discipline,
    and completeness remain open.
39b. Lane C model theory now has MC3-Lean pointwise model-hom composition laws,
    term/argument evaluation preservation, and positive quantifier-free formula
    satisfaction preservation. Formal counterexamples now show that ordinary
    model homomorphisms do not preserve negation, implication, or universal
    quantification without stronger hypotheses. Model isomorphisms now have
    identity, composition, predicate reflection, assignment-update transport,
    and full formula satisfaction equivalence. Formula translations now have
    identity, composition, one-way premise-list satisfaction preservation, and
    transported semantic-entailment instances for source assignments.
    Translation reflection, unrestricted target-side semantic-entailment
    preservation, and global finite search remain open.
40. Gate 10 has empirical operationalization artifacts at EMP0:
    coding manual, dataset schema, measurement protocol, reliability plan,
    validity plan, pilot protocol, and replication plan are drafted. No
    empirical validation is claimed.
41. Gate 11 has internal academic-rigor preparation artifacts: literature
    comparison matrix, reducibility audit, related-work map, external-review
    packet, and claims/limitations statement are drafted. External review has
    still not occurred.

## Reward-Hacking Risks

- Treating contradiction as insight.
- Treating evaluator acceptance as truth.
- Treating ISF as guilt.
- Treating M8 as harm or discrimination.
- Treating Lean verification as empirical validation.
- Treating a formal score as legitimacy.

## Repair Plan

1. Add many-sorted syntax.
2. Add assignments and satisfaction.
3. Prove finite kernel soundly embeds into the many-sorted model.
4. Add countermodel generator or finite enumeration.
5. Expand M8 with typed power objects.
6. Add normative bridge modules as optional, explicit extensions.
7. Add empirical coding artifacts only after definitions stabilize.
