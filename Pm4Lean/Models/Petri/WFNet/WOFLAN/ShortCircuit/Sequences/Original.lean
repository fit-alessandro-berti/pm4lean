import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Sequences.Definitions

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem firingSequence_original_to_shortCircuit
    {M M' : W.Marking} {ts : List W.net.Transition}
    (hSeq : FiringSequence W.net M ts M') :
    FiringSequence (shortCircuit W) M
      (ShortCircuitTransition.ofOriginalList W ts) M' := by
  induction hSeq with
  | nil M =>
      exact FiringSequence.nil (N := shortCircuit W) M
  | cons hEnabled hTail ih =>
      exact FiringSequence.cons
        ((original_enabled_iff W _ _).2 hEnabled)
        (by simpa [fire_original] using ih)

end shortCircuit

end Petri
end Pm4Lean
