import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth.Accumulation

namespace Pm4Lean
namespace Petri

theorem extra_final_cover_accumulated_growth_at_implies_linear_pump_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p)
    (hAccum : ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ExtraFinalCoverLinearPumpAt W M p := by
  intro hExtra n
  obtain ⟨M', hReach, hAccumLe⟩ := hAccum hExtra n
  have hNLeAccum : n ≤ W.initial p + n * (M p - W.final p) :=
    Nat.le_trans
      (Nat.le_mul_of_pos_right (m := M p - W.final p) n hPositive)
      (Nat.le_add_left _ _)
  exact ⟨M', hReach, Nat.le_trans hNLeAccum hAccumLe⟩

theorem extra_final_cover_accumulated_growth_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hAccum :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    extra_final_cover_accumulated_growth_at_implies_linear_pump_at
      hPositive (hAccum p hPositive)⟩

theorem extra_final_cover_closedFormGrowth_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p :=
  extra_final_cover_accumulated_growth_implies_linear_pump
    hExtra
    (extra_final_cover_closedFormGrowth_implies_accumulated_growth
      hClosed)

theorem extra_final_cover_accumulation_plan_at_implies_linear_pump_at
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p)
    (hPlan : ExtraFinalCoverAccumulationPlanAt W M p) :
    ExtraFinalCoverLinearPumpAt W M p :=
  extra_final_cover_accumulated_growth_at_implies_linear_pump_at
    hPositive
    (extra_final_cover_accumulation_plan_at_implies_accumulated_growth_at
      hPlan)

theorem extra_final_cover_accumulation_plan_implies_linear_pump
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    extra_final_cover_accumulation_plan_at_implies_linear_pump_at
      hPositive (hPlan p hPositive)⟩

end Petri
end Pm4Lean
