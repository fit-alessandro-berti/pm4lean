import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth.ClosedForm.Return

namespace Pm4Lean
namespace Petri

theorem extra_final_cover_implies_closedFormStep
    {W : WFNet} {M : W.Marking} :
    ExtraFinalCoverClosedFormStep W M := by
  intro hExtra n
  let R : W.Marking := M - W.final
  have hReachToM :
      Reachable (shortCircuit W) W.initial M :=
    shortCircuit.reachable_original_to_shortCircuit W hExtra.1
  have hReachWithAccumulated :
      Reachable (shortCircuit W)
        (W.initial + Marking.scale n R)
        (M + Marking.scale n R) :=
    Reachable.add_right hReachToM (Marking.scale n R)
  have hFinalCoveredAccumulated :
      W.final ≤ M + Marking.scale n R := by
    intro p
    exact Nat.le_trans (hExtra.2.1 p)
      (Nat.le_add_right (M p) (Marking.scale n R p))
  have hReturn :
      Reachable (shortCircuit W)
        (M + Marking.scale n R)
        ((M + Marking.scale n R) - W.final + W.initial) :=
    shortCircuit.reachable_fire_return_of_final_covered
      W hFinalCoveredAccumulated
  have hEq :
      (M + Marking.scale n R) - W.final + W.initial =
        W.initial + Marking.scale (n + 1) R := by
    simpa [R] using
      extra_final_cover_return_accumulated_eq
        (W := W) (M := M) hExtra.2.1 n
  exact Reachable.trans hReachWithAccumulated (by
    simpa [R, hEq] using hReturn)

end Petri
end Pm4Lean
