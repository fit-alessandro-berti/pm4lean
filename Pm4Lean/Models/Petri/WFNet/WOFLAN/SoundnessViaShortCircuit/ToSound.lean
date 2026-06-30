import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Forward

namespace Pm4Lean
namespace Petri

theorem live_shortCircuit_and_proper_completion_implies_sound
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hProper : ProperCompletion W) :
    Sound W :=
  ⟨live_shortCircuit_and_proper_completion_implies_option_to_complete
      hLive hProper,
    hProper,
    live_shortCircuit_and_proper_completion_implies_no_dead
      hLive hProper⟩

theorem live_shortCircuit_and_no_extra_final_cover_implies_sound
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hNoExtra :
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (no_extra_tokens_at_final_cover_implies_proper_completion hNoExtra)

theorem live_shortCircuit_and_no_extra_final_cover_statement
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hNoExtra :
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M) :
    Sound W ∧ Live (shortCircuit W) W.initial :=
  ⟨live_shortCircuit_and_no_extra_final_cover_implies_sound
      hLive hNoExtra,
    hLive⟩

theorem live_and_bounded_shortCircuit_implies_sound_of_no_extra
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_no_extra
      hLive hBounded hNoExtra)

theorem live_and_bounded_shortCircuit_implies_sound_of_pumping
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_pumping
      hPump hLive hBounded)

theorem live_and_bounded_shortCircuit_implies_sound_of_linear_pumping
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_linear_pumping
      hLinear hLive hBounded)

theorem live_and_bounded_shortCircuit_implies_sound_of_accumulated_growth
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_accumulated_growth
      hAccum hLive hBounded)

theorem live_and_bounded_shortCircuit_implies_sound_of_closedFormGrowth
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_closedFormGrowth
      hClosed hLive hBounded)

theorem live_and_bounded_shortCircuit_implies_sound_of_closedFormStep
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_closedFormStep
      hStep hLive hBounded)

theorem live_and_bounded_shortCircuit_implies_sound_of_accumulation_plan
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion_of_accumulation_plan
      hPlan hLive hBounded)

end Petri
end Pm4Lean
