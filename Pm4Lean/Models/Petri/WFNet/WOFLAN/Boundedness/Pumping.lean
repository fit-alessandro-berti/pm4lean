import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Growth

namespace Pm4Lean
namespace Petri

/--
An extra final-cover marking can be pumped in the short-circuited net past
every proposed global token bound.
-/
def ExtraFinalCoverPumpsAboveEveryBound (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ k : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        ∃ p : W.net.Place, k < M' p

theorem extra_final_cover_linear_pump_at_implies_pumps_above_every_bound
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p) :
    ExtraFinalCoverPumpsAboveEveryBound W M := by
  intro hExtra k
  obtain ⟨M', hReach, hLe⟩ := hLinear hExtra (k + 1)
  exact ⟨M', hReach, p, Nat.lt_of_succ_le hLe⟩

theorem extra_final_cover_linear_pump_implies_pumps_above_every_bound
    {W : WFNet} {M : W.Marking}
    (hLinear : ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ExtraFinalCoverPumpsAboveEveryBound W M := by
  obtain ⟨p, hPumpAt⟩ := hLinear
  exact extra_final_cover_linear_pump_at_implies_pumps_above_every_bound
    hPumpAt

theorem extra_final_cover_linear_pump_at_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  linearTokenGrowthAt_not_bounded (N := shortCircuit W)
    (M₀ := W.initial) (p := p) (hLinear hExtra)

theorem extra_final_cover_linear_pump_at_not_boundedBy
    {W : WFNet} {M : W.Marking} {p : W.net.Place}
    (hLinear : ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M)
    (k : Nat) :
    ¬ BoundedBy (shortCircuit W) W.initial k :=
  linearTokenGrowthAt_not_boundedBy (N := shortCircuit W)
    (M₀ := W.initial) (p := p) (hLinear hExtra) k

theorem extra_final_cover_pumping_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hPump : ExtraFinalCoverPumpsAboveEveryBound W M)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  not_bounded_of_forall_bound_reachable_gt (hPump hExtra)

theorem extra_final_cover_linear_pump_implies_shortCircuit_unbounded
    {W : WFNet} {M : W.Marking}
    (hLinear : ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ¬ Bounded (shortCircuit W) W.initial :=
  extra_final_cover_pumping_implies_shortCircuit_unbounded
    (extra_final_cover_linear_pump_implies_pumps_above_every_bound hLinear)
    hExtra

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
