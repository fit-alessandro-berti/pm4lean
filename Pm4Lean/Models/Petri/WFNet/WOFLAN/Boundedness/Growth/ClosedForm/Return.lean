import Pm4Lean.Models.Petri.Semantics.Monotonicity
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth.Definitions

namespace Pm4Lean
namespace Petri

theorem extra_final_cover_return_accumulated_eq
    {W : WFNet} {M : W.Marking}
    (hFinalCovered : W.final ≤ M) (n : Nat) :
    (M + Marking.scale n (M - W.final)) - W.final + W.initial =
      W.initial + Marking.scale (n + 1) (M - W.final) := by
  apply Marking.ext
  intro p
  calc
    ((M + Marking.scale n (M - W.final)) - W.final + W.initial) p =
        (M p + n * (M p - W.final p)) - W.final p + W.initial p := rfl
    _ = W.initial p + (n + 1) * (M p - W.final p) := by
        rw [Nat.sub_add_comm (hFinalCovered p)]
        rw [Nat.succ_mul]
        omega
    _ = (W.initial + Marking.scale (n + 1) (M - W.final)) p := rfl

end Petri
end Pm4Lean
