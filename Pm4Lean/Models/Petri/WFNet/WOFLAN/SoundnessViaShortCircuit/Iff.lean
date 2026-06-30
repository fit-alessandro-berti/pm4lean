import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Forward
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.ToSound

namespace Pm4Lean
namespace Petri

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSound
    exact sound_implies_live_and_bounded_shortCircuit_of_original_bounded
      hSound hBoundOriginal
  · intro hLiveBounded
    exact live_and_bounded_shortCircuit_implies_sound_of_no_extra
      hLiveBounded.1 hLiveBounded.2 hNoExtra

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  exact
    sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
      hBoundOriginal
      (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

end Petri
end Pm4Lean
