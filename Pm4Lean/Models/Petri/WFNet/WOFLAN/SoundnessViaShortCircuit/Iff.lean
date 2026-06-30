import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Forward
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.ToSound

namespace Pm4Lean
namespace Petri

theorem sound_iff_live_and_bounded_shortCircuit_of_original_bounded
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSound
    exact sound_implies_live_and_bounded_shortCircuit_of_original_bounded
      hSound hBoundOriginal
  · intro hLiveBounded
    exact live_and_bounded_shortCircuit_implies_sound
      hLiveBounded.1 hLiveBounded.2

theorem sound_and_original_bounded_iff_live_and_bounded_shortCircuit
    {W : WFNet} :
    Sound W ∧ TokenBoundedReachableOriginal W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSoundBounded
    exact sound_implies_live_and_bounded_shortCircuit_of_original_bounded
      hSoundBounded.1 hSoundBounded.2
  · intro hLiveBounded
    exact ⟨live_and_bounded_shortCircuit_implies_sound
      hLiveBounded.1 hLiveBounded.2,
      original_bounded_of_shortCircuit_bounded hLiveBounded.2⟩

end Petri
end Pm4Lean
