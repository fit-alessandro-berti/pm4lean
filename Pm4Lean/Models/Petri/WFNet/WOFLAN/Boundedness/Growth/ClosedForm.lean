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

theorem extra_final_cover_closedFormStep_implies_closedFormGrowth
    {W : WFNet} {M : W.Marking}
    (hStep : ExtraFinalCoverClosedFormStep W M) :
    ExtraFinalCoverClosedFormGrowth W M := by
  intro hExtra n
  let F : Nat → W.Marking :=
    fun k => W.initial + Marking.scale k (M - W.final)
  have hReachFromF0 :
      Reachable (shortCircuit W) (F 0) (F n) :=
    Reachable.of_nat_chain (N := shortCircuit W) F (hStep hExtra) n
  have hF0 : F 0 = W.initial := by
    simp [F, Marking.scale_zero, Marking.add_zero]
  simpa [F, hF0] using hReachFromF0

end Petri
end Pm4Lean
