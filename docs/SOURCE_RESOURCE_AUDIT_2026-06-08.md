# Source Resource Audit - 2026-06-08

Status: local source audit completed for the current attached resources.

## Resources Checked

- `C:\Users\virgin\Downloads\Paralogic - Request for Agent Instructions.pdf`
- `C:\Users\virgin\.codex\attachments\64733f84-bf8e-4ef7-b3d2-c94d15220847\pasted-text.txt`
- `C:\Users\virgin\.codex\attachments\5b1ef9a3-acb4-47cf-b9ae-7200c7b4a317\pasted-text.txt`
- `C:\Users\virgin\.codex\attachments\0066e1bb-54e5-46ce-a834-aba7744d3985\pasted-text.txt`
- `C:\Users\virgin\.codex\attachments\a093bb0e-37ea-4030-800c-3aaa5153b917\pasted-text.txt`

## Mechanism Names Found

The master pasted prompt lists the intended M1-M12 mechanism names:

| Mechanism | Name |
| --- | --- |
| M1 | Evidence Overclaim |
| M2 | Metric-as-Value Collapse |
| M3 | Formal Access Substitution |
| M4 | Symbolic Substitution |
| M5 | Repair Failure |
| M6 | Translation Failure |
| M7 | Category Essentialization |
| M8 | Power Erasure |
| M9 | Veto Suppression |
| M10 | Frame Drift |
| M11 | Symbolic Overload |
| M12 | Legitimacy Claim Decay |

Lean encoding added: `mechanismName`.

## Workbook Acceptance Status Found

The PDF states that the prior workbook accepts M1, M2, M3, M4, M5, M6, M7,
M9, M10, and M11, while M8 and M12 are not accepted yet.

Lean encoding added:

- `WorkbookMechanismStatus`
- `workbookMechanismStatus`
- `WorkbookAcceptedMechanism`
- `WorkbookPendingMechanism`
- `workbook_M1_accepted` through `workbook_M11_accepted` for the accepted
  workbook mechanisms, excluding M8 and M12
- `workbook_M8_pending`
- `workbook_M12_pending`
- `workbook_M8_not_accepted`
- `workbook_M12_not_accepted`

## Detail Gap

The available local resources provide mechanism names and acceptance status,
but not enough formal semantic detail to responsibly complete source-backed
semantics for M1-M7, M9-M11, or M12.  The same resources give more detailed
requirements for M8 power erasure, which is why the current repository has a
partial M8 power profile but should not claim M8 is globally accepted.

## Anti-Reward-Hacking Rule

Do not infer full semantics from names alone.  A mechanism name, a prior
workbook acceptance status, or a draft target is not a Lean-checked semantic
definition and is not empirical validation.

