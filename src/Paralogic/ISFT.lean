/-!
ISFT kernel and M8 power-erasure fragment.
-/

import Paralogic.Semantics

namespace Paralogic

structure ISF (w : World) : Prop where
  uses : w.uses
  claims : w.claims
  supportDegraded : w.supportDegraded
  treatsAsAdequate : w.treatsAsAdequate

structure M8 (w : World) : Prop where
  uses : w.uses
  claims : w.claims
  powerRelevant : w.powerRelevant
  powerValidityDependence : w.powerValidityDependence
  powerOmitted : w.powerOmitted
  supportDegraded : w.supportDegraded
  treatsAsAdequate : w.treatsAsAdequate

theorem ISF_to_Uses {w : World} (h : ISF w) : w.uses := h.uses
theorem ISF_to_Claims {w : World} (h : ISF w) : w.claims := h.claims
theorem ISF_to_SupportDegraded {w : World} (h : ISF w) : w.supportDegraded :=
  h.supportDegraded
theorem ISF_to_TreatsAsAdequate {w : World} (h : ISF w) : w.treatsAsAdequate :=
  h.treatsAsAdequate

theorem M8_to_ISF {w : World} (h : M8 w) : ISF w :=
  { uses := h.uses
    claims := h.claims
    supportDegraded := h.supportDegraded
    treatsAsAdequate := h.treatsAsAdequate }

theorem M8_to_Uses {w : World} (h : M8 w) : w.uses := h.uses
theorem M8_to_Claims {w : World} (h : M8 w) : w.claims := h.claims
theorem M8_to_PowerRelevant {w : World} (h : M8 w) : w.powerRelevant :=
  h.powerRelevant

end Paralogic
