# CALM / Paper Armies Source Dossier

## Status

This dossier is generated from `paper_armies_calm_source_map_v1.xlsx`. It turns
the spreadsheet into an auditable source-dossier package, but it does not claim
that every source has been captured or that every chapter claim is
manuscript-ready.

The current governing rule is strict: no primary factual manuscript claim is
ready until it has direct source capture, page-level extraction, counter-evidence
review, and source maturity S5 or stronger.

## Inventory

- Master source rows: 53
- Case/source-cluster rows: 15
- Capture gaps: 9
- Critical source rows: 18
- High source rows: 23
- Medium source rows: 12

## Source Classes

| Class | Count |
| --- | --- |
| discovery_or_narrative | 3 |
| external_evidence_target | 27 |
| internal_methodology | 7 |
| policy_or_theory_support | 12 |
| supporting_source_target | 4 |

## Readiness Classes

| Readiness | Count |
| --- | --- |
| capture_or_page_extraction_required | 37 |
| methodology_only_not_case_evidence | 7 |
| triage_required | 9 |

## Captured Source Packets

Current source packets are verified public anchors, not manuscript-ready page
extractions:

- `source_packets/s009_future_combat_systems_rand.md`
- `source_packets/s005_gao_f35_modernization.md`
- `source_packets/s008_gao_lcs_testing_weight.md`
- `source_packets/s017_nist_ai_rmf.md`
- `source_packets/s018_dod_cdao_ai.md`
- `source_packets/s019_dodd_3000_09_autonomy.md`
- `source_packets/s044_nist_sp_800_37_rmf.md`

## Initial Page Extractions

Initial page extractions are stronger than source anchors, but still not
manuscript-ready until counter-evidence, quote selection, and chapter-level
claim review are complete:

- `page_extractions/s005_gao_f35_modernization.md`
- `page_extractions/s008_gao_lcs_testing_weight.md`

## Critical Source Queue

| ID | Source Family | Specific Source / Document | Paper Armies Use | CALM Mapping | Next Action |
| --- | --- | --- | --- | --- | --- |
| S001 | SIGAR / Afghanistan | SIGAR Lessons Learned Program; especially What We Need to Learn and related Afghanistan reconstruction lessons | Macro anchor for claim economy, progress narratives, training, reconstruction claims, and institutional learning failure | Claim Receipt; Shadow Ledger; Lesson-to-Claim Conversion; Reflexivity Defense | Capture direct PDFs; extract page-level findings; map to Chapters 1, 8, 13, 18 |
| S003 | SIGIR / Iraq Reconstruction | SIGIR Hard Lessons: The Iraq Reconstruction Experience | Paper projects, reconstruction claims, contractor/government oversight, sustainment and local conditions | Validity Boundary; Consequence Trail; Sustainment as Truth | Capture PDF; extract cases for sustainment, contracting, and paper modernization chapters |
| S004 | Commission on Wartime Contracting | Transforming Wartime Contracting final report | Contracting waste, accountability fragmentation, fraud/waste/abuse, consequence laundering | Consequence Trail; Ownership-to-Stewardship; Source Maturity Tracker | Capture final report PDF; map findings to contractor-government incentive chapter |
| S005 | GAO / F-35 | GAO F-35 sustainment, mission capable rates, modernization, and lifecycle cost reports | Modernization, readiness, sustainment debt, software, spares, contractor logistics, lifecycle burden | Sustainment as Truth; Validity Boundary; Expiration Trigger | Identify newest and most relevant GAO reports; extract readiness/sustainment language |
| S008 | Littoral Combat Ship | GAO, CRS, DOT&E materials on LCS mission modules, survivability, maintenance, and concept changes | Architecture of claim-stack collapse: speed, modularity, littoral relevance, mine warfare, crew, survivability, sustainment | Category Machine; Prototype Stage; Sustainment as Truth | Capture CRS report ID and GAO/DOT&E direct PDFs |
| S009 | Future Combat Systems | RAND Lessons from the Army's Future Combat Systems Program | Complex modernization, requirements ambition, system-of-systems fragility, future war concepts | System-of-Systems; Category Machine; Validity Load | Capture RAND PDF; extract SOF failure patterns and overclaim guards |
| S012 | JADC2 / CJADC2 | DoD JADC2/CJADC2 strategy and GAO/CRS oversight | Interoperability and command-and-control claims under coalition, data, authority, and cyber constraints | Interoperability Without Theater; Boundary Integrity | Capture official strategy, GAO/CRS oversight, service docs |
| S017 | NIST AI RMF | NIST Artificial Intelligence Risk Management Framework 1.0 | AI risk framing, trustworthiness, validity, reliability, monitoring, governance | AI Without Aura; Metric Integrity; Evidence Boundary | Capture PDF and crosswalk NIST categories to CALM AI chapter |
| S018 | DoD Responsible AI | DoD Responsible AI Strategy and Implementation Pathway; RAI Toolkit | Responsible AI governance, traceability, reliability, governability, bias, accountability | AI Without Aura; Human Role Boundary; Decision Guardrail | Capture exact documents and dates; map to AI chapter |
| S019 | DoDD 3000.09 | Autonomy in Weapon Systems directive | Autonomous systems policy, human judgment, weapon system governance | AI Without Aura; Bounded Authorization; Legal/Authority Boundary | Capture current directive and relevant pages |
| S035 | 507th Maintenance Company | Official Army report on attack on the 507th Maintenance Company; public survivor/reporting | Human-cost interlude: wrong turn, communication, mission representation, convoy vulnerability | Human Boundary; Validity Boundary; Consequence Trail | Capture official report, maps, casualty details from public record |
| S036 | Tongo Tongo | DoD unclassified executive summary/investigation on Niger ambush | Human-cost interlude: mission change, ISR/QRF/medevac, risk representation | Human Boundary; Mission Claim; Expiration Trigger | Capture DoD report and timeline; build ethical packet |
| S037 | Pat Tillman | DoD IG report, Army investigations, congressional/public record | Human-cost interlude: public narrative, friendly fire, reporting, trust | Claim Engine; Public Narrative Boundary; Consequence Trail | Capture DoD IG and congressional documents |
| S038 | Wanat / COP Kahler | Combat Studies Institute report and Army investigations | Human-cost interlude: outpost as claim, force protection, terrain, command decisions | Validity Boundary; Human Boundary; Consequence Trail | Capture CSI report and investigation materials |
| S039 | MRAP Rapid Fielding | GAO/DoD/Marine Corps sources on MRAP rapid acquisition and fielding | Countercase: speed can work when urgency, evidence, authority, and delivery align | Countercase; Rapid Fielding; Learning Mobility | Build countercase packet with official sources |
| S042 | DoD Adaptive Acquisition Framework | DoD AAF official guidance / DAU materials | Method integration: acquisition pathways, milestone logic, software/hardware paths | Method Integration; Claim Receipt; No Dual-Running | Crosswalk CALM instruments to AAF pathways |
| S044 | RMF / ATO / cATO | DoD RMF knowledge service/public docs, NIST SP 800-37, cATO guidance where public | Cyber authorization, compliance vs operational cyber resilience, bounded authorization | Cyber Boundary; Decision Guardrail; Bounded Authorization | Capture public RMF/cATO docs; crosswalk with CALM |
| S052 | CALM v5.0 Hardened Baseline | Uploaded CALM Master Baseline Specification v5.0 Hardened | Current system baseline for five CALM families, H1-H8 hardening rules, Reflexivity Trap | All CALM system families | Use as current controlling internal architecture |

## Dossier Files

- `source_register.csv` - normalized master source map.
- `case_claim_map.csv` - normalized case-to-claim map.
- `calm_applicability.csv` - CALM component/source-pattern mapping.
- `capture_gaps.csv` - open source and evidence gaps.
- `chapter_source_matrix.csv` - chapter-to-case support matrix.
- `case_packets/` - one packet per case/source cluster.
- `source_packets/` - captured source packets as public anchors and page-level
  extraction work are completed.
- `SOURCE_CAPTURE_LOG.md` - source-capture progress and readiness levels.
- `manuscript_readiness_audit.md` - anti-reward-hacking readiness audit.

## Usefulness Check

This dossier gives Paper Armies and CALM a source-control layer. It separates
external evidence from internal methodology, prevents discovery sources from
becoming factual proof, and gives each case a bounded role before drafting.

## Claim Boundary

This dossier does not prove the book thesis, does not validate CALM, does not
complete source capture, and does not authorize factual claims unsupported by
page-level public evidence.
