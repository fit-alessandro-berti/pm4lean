import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth.ClosedForm

namespace Pm4Lean
namespace Petri

theorem extra_final_cover_closedFormGrowth_implies_accumulated_growth_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro hExtra n
  exact ⟨W.initial + Marking.scale n (M - W.final),
    hClosed hExtra n,
    Nat.le_refl _⟩

theorem extra_final_cover_closedFormGrowth_implies_accumulated_growth
    {W : WFNet} {M : W.Marking}
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ∀ p : W.net.Place,
      0 < M p - W.final p →
        ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro p _hPositive
  exact extra_final_cover_closedFormGrowth_implies_accumulated_growth_at
    hClosed

theorem extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPlan : ExtraFinalCoverAccumulationPlanAt W M p) :
    ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro hExtra n
  obtain ⟨F, hStart, hStep, hGrowth⟩ := hPlan hExtra
  have hReachFromStart :
      Reachable (shortCircuit W) (F 0) (F n) :=
    Reachable.of_nat_chain (N := shortCircuit W) F hStep n
  have hReach :
      Reachable (shortCircuit W) W.initial (F n) := by
    simpa [hStart] using hReachFromStart
  exact ⟨F n, hReach, hGrowth n⟩

theorem extra_final_cover_accumulation_plan_implies_accumulated_growth
    {W : WFNet} {M : W.Marking}
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ∀ p : W.net.Place,
      0 < M p - W.final p →
        ExtraFinalCoverAccumulatedGrowthAt W M p := by
  intro p hPositive
  exact extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
    (hPlan p hPositive)

end Petri
end Pm4Lean
