import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness

namespace Pm4Lean
namespace Petri

/--
The standard WOFLAN target theorem will relate WF-net soundness to liveness
and boundedness of the short-circuited marked net.  This predicate records the
statement shape while the full proof is developed.
-/
def SoundnessViaShortCircuitStatement (W : WFNet) : Prop :=
  WFNetStructure W →
    (Sound W ↔
      Live (shortCircuit W) W.initial ∧ Bounded (shortCircuit W) W.initial)

def StructuredSoundnessViaShortCircuitStatement
    (W : StructuredWFNet) : Prop :=
  Sound W.wfnet ↔
    Live (shortCircuit W.wfnet) W.wfnet.initial ∧
      Bounded (shortCircuit W.wfnet) W.wfnet.initial

theorem sound_implies_live_and_bounded_shortCircuit_of_original_bounded
    {W : WFNet}
    (hSound : Sound W)
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial :=
  ⟨live_of_sound hSound,
    shortCircuit_bounded_of_original_bounded_and_sound
      hBoundOriginal hSound⟩

theorem sound_implies_live_and_bounded_shortCircuit_of_original_tokenSum_bounded
    {W : WFNet}
    (hSound : Sound W)
    (hBoundOriginal : TokenSumBoundedReachableOriginal W) :
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial :=
  ⟨live_of_sound hSound,
    shortCircuit_bounded_of_original_tokenSum_bounded_and_sound
      hBoundOriginal hSound⟩

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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSound
    exact sound_implies_live_and_bounded_shortCircuit_of_original_tokenSum_bounded
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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPump

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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_linear_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hLinear

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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulated_growth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hAccum

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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormGrowth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hClosed

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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
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

theorem sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulation_plan
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPlan

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    SoundnessViaShortCircuitStatement W := by
  unfold SoundnessViaShortCircuitStatement
  intro _hStruct
  exact sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal hNoExtra

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    SoundnessViaShortCircuitStatement W := by
  unfold SoundnessViaShortCircuitStatement
  intro _hStruct
  exact
    sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
      hBoundOriginal hNoExtra

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPump

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_linear_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hLinear

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_accumulated_growth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hAccum

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_closedFormGrowth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hClosed

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem soundnessViaShortCircuitStatement_of_original_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

theorem soundnessViaShortCircuitStatement_of_original_tokenSum_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    SoundnessViaShortCircuitStatement W :=
  soundnessViaShortCircuitStatement_of_original_bounded_and_accumulation_plan
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPlan

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W.wfnet) :
    StructuredSoundnessViaShortCircuitStatement W :=
  sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal hNoExtra

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W.wfnet) :
    StructuredSoundnessViaShortCircuitStatement W :=
  sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
    hBoundOriginal hNoExtra

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_pumping
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hPump :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverPumpsAboveEveryBound W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_pumping
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hPump :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverPumpsAboveEveryBound W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPump

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_linear_pumping
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hLinear :
      ∀ M : W.wfnet.Marking,
        ∃ p : W.wfnet.net.Place,
          ExtraFinalCoverLinearPumpAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_linear_pumping
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hLinear :
      ∀ M : W.wfnet.Marking,
        ∃ p : W.wfnet.net.Place,
          ExtraFinalCoverLinearPumpAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_linear_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hLinear

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulated_growth
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hAccum :
      ∀ M : W.wfnet.Marking,
        HasExtraTokensAtFinalCover W.wfnet M →
          ∀ p : W.wfnet.net.Place,
            0 < M p - W.wfnet.final p →
              ExtraFinalCoverAccumulatedGrowthAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_accumulated_growth
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hAccum :
      ∀ M : W.wfnet.Marking,
        HasExtraTokensAtFinalCover W.wfnet M →
          ∀ p : W.wfnet.net.Place,
            0 < M p - W.wfnet.final p →
              ExtraFinalCoverAccumulatedGrowthAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulated_growth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hAccum

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormGrowth
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hClosed :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverClosedFormGrowth W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_closedFormGrowth
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hClosed :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverClosedFormGrowth W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormGrowth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hClosed

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_closedFormStep
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hStep :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverClosedFormStep W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_closedFormStep
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hStep :
      ∀ M : W.wfnet.Marking,
        ExtraFinalCoverClosedFormStep W.wfnet M) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulation_plan
    {W : StructuredWFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W.wfnet)
    (hPlan :
      ∀ M : W.wfnet.Marking,
        HasExtraTokensAtFinalCover W.wfnet M →
          ∀ p : W.wfnet.net.Place,
            0 < M p - W.wfnet.final p →
              ExtraFinalCoverAccumulationPlanAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

theorem structured_sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_accumulation_plan
    {W : StructuredWFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W.wfnet)
    (hPlan :
      ∀ M : W.wfnet.Marking,
        HasExtraTokensAtFinalCover W.wfnet M →
          ∀ p : W.wfnet.net.Place,
            0 < M p - W.wfnet.final p →
              ExtraFinalCoverAccumulationPlanAt W.wfnet M p) :
    StructuredSoundnessViaShortCircuitStatement W :=
  structured_sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_accumulation_plan
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPlan

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial := by
  have hBehavior :
      Sound W ↔
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
    sound_iff_live_and_bounded_shortCircuit_of_original_bounded_and_no_extra
      hBoundOriginal hNoExtra
  constructor
  · intro hClassical
    exact ⟨hClassical.1, hBehavior.1 hClassical.2⟩
  · intro hStructLiveBounded
    exact ⟨hStructLiveBounded.1, hBehavior.2 hStructLiveBounded.2⟩

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_no_extra
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hNoExtra : ShortCircuitBoundedExcludesExtraFinalCover W) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial := by
  have hBehavior :
      Sound W ↔
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
    sound_iff_live_and_bounded_shortCircuit_of_original_tokenSum_bounded_and_no_extra
      hBoundOriginal hNoExtra
  constructor
  · intro hClassical
    exact ⟨hClassical.1, hBehavior.1 hClassical.2⟩
  · intro hStructLiveBounded
    exact ⟨hStructLiveBounded.1, hBehavior.2 hStructLiveBounded.2⟩

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_pumping hPump)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPump : ∀ M : W.Marking, ExtraFinalCoverPumpsAboveEveryBound W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPump

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_linear_pumping
      hLinear)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_linear_pumping
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hLinear :
      ∀ M : W.Marking,
        ∃ p : W.net.Place, ExtraFinalCoverLinearPumpAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_linear_pumping
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hLinear

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulated_growth
      hAccum)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_accumulated_growth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hAccum :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulatedGrowthAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_accumulated_growth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hAccum

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormGrowth
      hClosed)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_closedFormGrowth
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hClosed :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormGrowth W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_closedFormGrowth
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hClosed

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_closedFormStep
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hStep :
      ∀ M : W.Marking, ExtraFinalCoverClosedFormStep W M) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_closedFormStep
      hStep)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_no_extra
    hBoundOriginal
    (shortCircuit_bounded_excludes_extra_final_cover_of_accumulation_plan
      hPlan)

theorem classical_soundness_iff_structure_and_live_bounded_of_original_tokenSum_bounded_and_accumulation_plan
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hPlan :
      ∀ M : W.Marking,
        HasExtraTokensAtFinalCover W M →
          ∀ p : W.net.Place,
            0 < M p - W.final p →
              ExtraFinalCoverAccumulationPlanAt W M p) :
    ClassicalSoundness W ↔
      WFNetStructure W ∧
        Live (shortCircuit W) W.initial ∧
          Bounded (shortCircuit W) W.initial :=
  classical_soundness_iff_structure_and_live_bounded_of_original_bounded_and_accumulation_plan
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hPlan

end Petri
end Pm4Lean
