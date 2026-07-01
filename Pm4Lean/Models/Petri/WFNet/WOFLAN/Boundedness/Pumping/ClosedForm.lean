import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Pumping.Linear

namespace Pm4Lean
namespace Petri

theorem extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hClosed : ExtraFinalCoverClosedFormGrowth W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    (extra_final_cover_closedFormGrowth_implies_linear_pump
      hExtra hClosed)
    hExtra

theorem extra_final_cover_closedFormStep_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hStep : ExtraFinalCoverClosedFormStep W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    hExtra
    (extra_final_cover_closedFormStep_implies_closedFormGrowth hStep)

theorem extra_final_cover_accumulation_plan_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M)
    (hPlan :
      ∀ p : W.net.Place,
        0 < M p - W.final p →
          ExtraFinalCoverAccumulationPlanAt W M p) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    (extra_final_cover_accumulation_plan_implies_linear_pump
      hExtra hPlan)
    hExtra

end Petri
end Pm4Lean
