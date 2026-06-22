# CALM Formal Guard Specification

## Status

This file explains the initial Lean module `src/Paralogic/CALM.lean`. The
module is a checked guard schema for selected CALM ideas. It is not empirical
validation, not a complete doctrine, and not proof that CALM works in defense
organizations.

## Formal Objects

`ClaimReceipt` represents the minimum information a consequential claim must
carry before it can travel through an institution:

- evidence offered;
- boundary declared;
- negative space declared;
- consequence owner declared;
- expiration declared.

`LearningPacket` represents the minimum information local learning must carry
before CALM helps it travel:

- local use described;
- conditions declared;
- receiver identified;
- reuse barriers logged;
- stewardship owner declared;
- second-use plan declared.

`CALMImplementation` represents the reflexivity problem: CALM artifacts can be
completed while real decisions and learning remain unchanged.

## Checked Non-Collapse Results

The Lean module checks that:

1. missing evidence blocks claim travel;
2. missing boundary blocks claim travel;
3. missing negative space blocks claim travel;
4. missing consequence ownership blocks claim travel;
5. missing expiration blocks claim travel;
6. paper capability risk does not demonstrate operational validity;
7. claim travel readiness does not prove operational validity;
8. missing receiver blocks learning travel;
9. missing second-use plan blocks learning travel;
10. learning travel readiness does not prove second valid use;
11. artifacts alone do not pass Reflexivity Defense;
12. Paper CALM risk blocks reflexivity when burden reduction is absent.

## Relation To Paper Armies

The formal core supports the book's recurring non-collapse rule:

Representation does not become operational reality merely because it is
complete, visible, authorized, accepted, or repeated.

## Relation To CALM Toolkit

The checked objects map to future toolkit instruments:

| Lean object | Toolkit instrument |
| --- | --- |
| `ClaimReceipt` | Claim Receipt, Validity Boundary, Shadow Ledger, Consequence Trail |
| `LearningPacket` | Learning Escape Route, Reuse Barrier Log, Second-Use Plan |
| `CALMImplementation` | Reflexivity Audit Sheet, Paper CALM audit |

## Usefulness Check

This formal core blocks false inferences that ordinary process language often
permits: ready-to-travel does not mean operationally valid, captured learning
does not mean institutional learning, and completed CALM artifacts do not mean
CALM changed a real decision.

## Claim Boundary

The Lean module proves only selected logical guard properties over simplified
structures. It does not validate any real program, case, defense institution,
method profile, source packet, or implementation pilot.
