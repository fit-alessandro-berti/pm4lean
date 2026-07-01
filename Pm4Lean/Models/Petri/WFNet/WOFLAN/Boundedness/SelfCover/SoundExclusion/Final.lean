import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Unbounded

namespace Pm4Lean
namespace Petri

theorem final_plus_difference_ne_final_of_strict_cover
    {W : WFNet} {M M' : W.Marking}
    (hLe : M ≤ M') (hNe : M ≠ M') :
    W.final + (M' - M) ≠ W.final := by
  intro hEq
  obtain ⟨p, hLt⟩ := Marking.exists_lt_of_le_ne hLe hNe
  have hPositive : 0 < M' p - M p := Nat.sub_pos_of_lt hLt
  have hStrict :
      W.final p < (W.final + (M' - M)) p := by
    exact Nat.lt_add_of_pos_right hPositive
  rw [hEq] at hStrict
  exact Nat.lt_irrefl (W.final p) hStrict

end Petri
end Pm4Lean
