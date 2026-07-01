import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Reachability

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem fire_return_at_final :
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition =
      W.initial := by
  apply Marking.ext
  intro p
  calc
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition p
        = W.final p - W.final p + W.initial p := rfl
    _ = W.initial p := by rw [Nat.sub_self, Nat.zero_add]

theorem reachable_final_to_initial_in_shortCircuit :
    Reachable (shortCircuit W) W.final W.initial := by
  simpa [fire_return_at_final] using
    (Reachable.of_enabled (return_enabled_at_final W))

end shortCircuit

end Petri
end Pm4Lean
