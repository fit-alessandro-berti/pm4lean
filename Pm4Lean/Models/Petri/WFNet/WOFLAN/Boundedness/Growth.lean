import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.ExtraFinalCover

namespace Pm4Lean
namespace Petri

/--
An extra final-cover marking can be pumped linearly at a fixed place.  This is
the concrete repeated-growth obligation needed for the full WOFLAN
boundedness contradiction.
-/
def ExtraFinalCoverLinearPumpAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧ n ≤ M' p

/--
The repeated-return accumulation obligation for an extra final-cover marking:
after `n` cycles, the selected place carries at least its initial tokens plus
`n` copies of the extra remainder left by the return transition.
-/
def ExtraFinalCoverAccumulatedGrowthAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat, ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        W.initial p + n * (M p - W.final p) ≤ M' p

/--
Closed-form version of the repeated-return target: the short-circuited net can
reach the initial marking plus `n` copies of the extra remainder.
-/
def ExtraFinalCoverClosedFormGrowth (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W) W.initial
        (W.initial + Marking.scale n (M - W.final))

/--
Stepwise version of closed-form growth: each accumulated marking can reach the
next accumulated marking.
-/
def ExtraFinalCoverClosedFormStep (W : WFNet) (M : W.Marking) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∀ n : Nat,
      Reachable (shortCircuit W)
        (W.initial + Marking.scale n (M - W.final))
        (W.initial + Marking.scale (n + 1) (M - W.final))

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

/--
An operational plan for proving accumulated growth: provide a Nat-indexed
chain of short-circuit reachable cycles, starting at the initial marking, whose
token count at `p` grows by the extra remainder.
-/
def ExtraFinalCoverAccumulationPlanAt
    (W : WFNet) (M : W.Marking) (p : W.net.Place) : Prop :=
  HasExtraTokensAtFinalCover W M →
    ∃ F : Nat → W.Marking,
      F 0 = W.initial ∧
        (∀ n : Nat,
          Reachable (shortCircuit W) (F n) (F (n + 1))) ∧
        ∀ n : Nat,
          W.initial p + n * (M p - W.final p) ≤ F n p

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
