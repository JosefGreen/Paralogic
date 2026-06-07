# Status Discipline

This repository uses explicit proof and validation labels.

## Allowed Labels

- PS0: informal idea only.
- PS1: stated only.
- PS2: structured proof sketch.
- PS3: formal-text proof.
- PS4: externally reviewed mathematical proof.
- MC0: not machine-checkable yet.
- MC1: encodable with substantial work.
- MC2: proof-ready candidate.
- MC3-Lean: accepted by Lean or another trusted proof assistant.
- EFC: executable finite countermodel checked.
- EFE: executable finite entailment checked.
- PYC: Python custom proof-checker checked.
- EMP0: no empirical evidence.
- EMP1-EMP5: increasing empirical validation levels.

## Current Repository Status

- Paralogic / ISFT formal core: PS2/PS3 text fragments depending on module.
- Python finite ISFT/M8/ValidInsight checker: EFC/EFE/PYC for the encoded
  finite fragment.
- Lean sources: MC2 candidate only until `lake build` succeeds.
- MC3-Lean theorems: none claimed.
- Empirical validation: EMP0 for the formal system as a whole.
- External mathematical review: not yet recorded.

## Forbidden Claims

Do not claim:

- Paralogic is complete.
- Paralogic is Lean-verified.
- Paralogic is empirically validated.
- Paralogic proves truth, moral truth, or repair.
- ISFT proves wrongdoing, illegality, harm, or guilt.
- M8 proves discrimination, coercion, harm, illegality, moral guilt, or repair
  obligation.
- ValidInsight proves empirical truth.
- Evaluator approval proves correctness.
- Proof-ready means proof-checked.

## Permitted Claims

You may claim:

- The repository contains a typed formalization workbench.
- Selected definitional implications have executable finite checks.
- Selected non-entailments have executable finite countermodels.
- Lean candidate files exist.
- No Lean theorem is treated as MC3-Lean until Lean actually accepts it.
- No empirical validation is claimed.
