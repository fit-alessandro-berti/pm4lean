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

theorem live_and_bounded_shortCircuit_implies_sound
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    Sound W :=
  live_shortCircuit_and_proper_completion_implies_sound
    hLive
    (bounded_shortCircuit_implies_proper_completion hLive hBounded)

end Petri
end Pm4Lean
