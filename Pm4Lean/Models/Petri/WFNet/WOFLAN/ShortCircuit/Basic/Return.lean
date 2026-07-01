import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Basic.Definition

namespace Pm4Lean
namespace Petri

namespace shortCircuit

variable (W : WFNet)

theorem return_enabled_at_final :
    Enabled (shortCircuit W) W.final ShortCircuitTransition.returnTransition := by
  intro p
  exact Nat.le_refl (W.final p)

theorem return_enabled_iff_final_covered (M : W.Marking) :
    Enabled (shortCircuit W) M ShortCircuitTransition.returnTransition ↔
      W.final ≤ M :=
  Iff.rfl

theorem fire_return (M : W.Marking) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition =
      M - W.final + W.initial :=
  rfl

theorem fire_return_apply (M : W.Marking) (p : W.net.Place) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition p =
      M p - W.final p + W.initial p :=
  rfl

theorem remainder_le_fire_return (M : W.Marking) (p : W.net.Place) :
    M p - W.final p ≤
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.le_add_right _ _

theorem fire_return_positive_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    0 < fire (shortCircuit W) M ShortCircuitTransition.returnTransition p :=
  Nat.lt_of_lt_of_le hPositive (remainder_le_fire_return W M p)

theorem initial_lt_fire_return_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    W.initial p <
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.lt_add_of_pos_left hPositive

theorem reachable_fire_return_of_final_covered
    {M : W.Marking}
    (hFinalCovered : W.final ≤ M) :
    Reachable (shortCircuit W) M (M - W.final + W.initial) := by
  simpa [fire_return] using
    (Reachable.of_enabled
      ((return_enabled_iff_final_covered W M).2 hFinalCovered))

end shortCircuit

end Petri
end Pm4Lean
