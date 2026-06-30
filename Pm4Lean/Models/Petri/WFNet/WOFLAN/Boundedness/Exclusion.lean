import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Pumping

namespace Pm4Lean
namespace Petri

/--
The remaining WOFLAN boundedness obligation: in a live and bounded
short-circuited net, no reachable marking may cover the final marking while
carrying extra tokens.
-/
def ShortCircuitBoundedExcludesExtraFinalCover (W : WFNet) : Prop :=
  Live (shortCircuit W) W.initial →
    Bounded (shortCircuit W) W.initial →
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M

theorem shortCircuit_bounded_excludes_extra_final_cover_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W := by
  intro _hLive hBounded M hExtra
  exact extra_final_cover_pumping_implies_shortCircuit_unbounded
    (hPump M) hExtra hBounded

theorem shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_pumping
    (fun M =>
      extra_final_cover_linear_pump_implies_pumps_above_every_bound
        (hLinear M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    {W : WFNet}
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
    (fun M =>
      by
        by_cases hExtra : HasExtraTokensAtFinalCover W M
        · exact extra_final_cover_accumulated_growth_implies_linear_pump
            hExtra (hAccum M hExtra)
        · exact ⟨W.i, fun hFalse => False.elim (hExtra hFalse)⟩)

theorem shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    (fun M _hExtra =>
      extra_final_cover_closedFormGrowth_implies_accumulated_growth
        (hClosed M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
    (fun M =>
      extra_final_cover_closedFormStep_implies_closedFormGrowth
        (hStep M))

theorem shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    ShortCircuitBoundedExcludesExtraFinalCover W :=
  shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
    (fun M hExtra =>
      extra_final_cover_accumulation_plan_implies_accumulated_growth
        (hPlan M hExtra))

end Petri
end Pm4Lean
