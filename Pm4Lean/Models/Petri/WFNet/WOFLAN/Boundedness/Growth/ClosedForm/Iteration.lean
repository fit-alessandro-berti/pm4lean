import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth.ClosedForm.Step

namespace Pm4Lean
namespace Petri

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
