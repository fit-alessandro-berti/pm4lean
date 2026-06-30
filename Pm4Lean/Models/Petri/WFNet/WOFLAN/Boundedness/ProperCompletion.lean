import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Exclusion

namespace Pm4Lean
namespace Petri

theorem proper_completion_iff_no_extra_tokens_at_final_cover
    (W : WFNet) :
    ProperCompletion W ↔
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M := by
  constructor
  · intro hProper M hExtra
    exact hExtra.2.2 (hProper M hExtra.1 hExtra.2.1)
  · intro hNoExtra M hReach hFinalCovered
    classical
    by_cases hEq : M = W.final
    · exact hEq
    · exact False.elim (hNoExtra M ⟨hReach, hFinalCovered, hEq⟩)

theorem not_proper_completion_iff_exists_extra_tokens_at_final_cover
    (W : WFNet) :
    ¬ ProperCompletion W ↔
      ∃ M : W.Marking, HasExtraTokensAtFinalCover W M := by
  classical
  rw [proper_completion_iff_no_extra_tokens_at_final_cover W]
  constructor
  · intro hNotAllNoExtra
    by_cases hExists : ∃ M : W.Marking, HasExtraTokensAtFinalCover W M
    · exact hExists
    · exact False.elim (hNotAllNoExtra (by
        intro M hExtra
        exact hExists ⟨M, hExtra⟩))
  · intro hExists hAllNoExtra
    obtain ⟨M, hExtra⟩ := hExists
    exact hAllNoExtra M hExtra

theorem not_proper_completion_implies_shortCircuit_unbounded_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_pumping_implies_shortCircuit_unbounded
    (hPump M) hExtra

theorem not_proper_completion_implies_shortCircuit_unbounded_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial :=
  not_proper_completion_implies_shortCircuit_unbounded_of_pumping
    (fun M =>
      extra_final_cover_linear_pump_implies_pumps_above_every_bound
        (hLinear M))
    hNotProper

theorem not_proper_completion_implies_shortCircuit_unbounded_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_closedFormGrowth_implies_shortCircuit_unbounded
    hExtra (hClosed M)

theorem not_proper_completion_implies_shortCircuit_unbounded_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_closedFormStep_implies_shortCircuit_unbounded
    hExtra (hStep M)

theorem not_proper_completion_implies_shortCircuit_unbounded_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p)
    (hNotProper : ¬ ProperCompletion W) :
    ¬ Bounded (shortCircuit W) W.initial := by
  obtain ⟨M, hExtra⟩ :=
    (not_proper_completion_iff_exists_extra_tokens_at_final_cover W).1
      hNotProper
  exact extra_final_cover_accumulation_plan_implies_shortCircuit_unbounded
    hExtra (hPlan M hExtra)

theorem no_extra_tokens_at_final_cover_implies_proper_completion
    {W : WFNet}
    (hNoExtra : ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M) :
    ProperCompletion W :=
  (proper_completion_iff_no_extra_tokens_at_final_cover W).2 hNoExtra

theorem bounded_shortCircuit_implies_proper_completion_of_no_extra
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    ProperCompletion W :=
  no_extra_tokens_at_final_cover_implies_proper_completion
    (hNoExtra hLive hBounded)

theorem bounded_shortCircuit_implies_proper_completion_of_pumping
    {W : WFNet}
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem bounded_shortCircuit_implies_proper_completion_of_linear_pumping
    {W : WFNet}
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem bounded_shortCircuit_implies_proper_completion_of_accumulated_growth
    {W : WFNet}
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem bounded_shortCircuit_implies_proper_completion_of_closedFormGrowth
    {W : WFNet}
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem bounded_shortCircuit_implies_proper_completion_of_closedFormStep
    {W : WFNet}
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem bounded_shortCircuit_implies_proper_completion_of_accumulation_plan
    {W : WFNet}
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p)
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  bounded_shortCircuit_implies_proper_completion_of_no_extra
    hLive hBounded
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

end Petri
end Pm4Lean
