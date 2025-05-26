import Paralogic.Emanance
import Paralogic.Frames
import Paralogic.Jumps
import Paralogic.Stuckness

-/!
  src/Paralogic/NeuralJump.lean

  Neural-guided jump proposals: encoder, decoder, and loss function.
-/


namespace Paralogic.NeuralJump

variable {n k : ℕ} {δ : ℝ} (hδ : 0 < δ)

/--
Abstract type for neural network parameters.
-/
variable (β : Type*)

/--
A neural proposal consists of:
  • an encoder `E : (Fin n → ℝ) → β`, mapping state to parameters,
  • a decoder `D : β → List Paralogic.Frames.Constraint`, selecting constraints to jump on.
-/
structure NeuralProposal where
  E : (Fin n → ℝ) → β
  D : β → List Paralogic.Frames.Constraint

/--
Given a neural proposal `N`, a frame `F`, and a list of constraints `cs`,
`propose N F cs v` applies the jump operator on the constraints decoded by `N`,
starting from state `v`.
-/
def propose (N : NeuralProposal β) (F : Paralogic.Emanance.Frame n k)
  (cs : List Paralogic.Frames.Constraint) (v : Fin n → ℝ) : Fin n → ℝ :=
  Paralogic.Jumps.jumpOp hδ F (N.D (N.E v)) v

/--
Loss function for training: the reduction in insightScore achieved by `propose`.
We seek to maximize this, equivalently minimize the negative reduction.
-/
def loss (N : NeuralProposal β) (F : Paralogic.Emanance.Frame n k)
  (cs : List Paralogic.Frames.Constraint) (v : Fin n → ℝ) : ℝ :=
  Paralogic.Stuckness.insightScore hδ F cs v -
    Paralogic.Stuckness.insightScore hδ F cs (propose N F cs v)

end Paralogic.NeuralJump
