# Dependency Graph

```mermaid
flowchart TD
  Kernel["Shared Kernel: types, statuses, satisfaction"]
  Frame["Frame and Context Calculus"]
  Contra["Contradiction Calculus"]
  Eval["Evaluator Calculus"]
  Insight["ValidInsight / Delta Calculus"]
  Failure["Failure Taxonomy"]
  ISFT["ISFT Kernel: ISF"]
  M8["M8 Power Erasure"]
  Bridges["Normative Bridges"]
  Empirical["Empirical Validation"]
  Checker["Finite Checker"]
  Lean["Lean Candidate Layer"]

  Kernel --> Frame
  Kernel --> Contra
  Kernel --> Eval
  Frame --> Contra
  Contra --> Insight
  Eval --> Insight
  Insight --> Failure
  Kernel --> ISFT
  ISFT --> M8
  M8 --> Bridges
  ISFT --> Empirical
  Insight --> Checker
  ISFT --> Checker
  M8 --> Checker
  Kernel --> Lean
  Checker --> Lean
```

## Reading the Graph

The finite checker covers only selected definitional consequences of ISFT,
M8, and ValidInsight. It does not validate the whole graph. Lean is downstream
of the current signature work and cannot be treated as verified until the
candidate files build successfully.
