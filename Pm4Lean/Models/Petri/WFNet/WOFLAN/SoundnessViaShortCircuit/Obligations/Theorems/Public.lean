import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Iff
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_obligations
    {W : WFNet}
    (hObligations : WoflanProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_firingSequence_self_cover_extraction
    (unboundedOriginalProducesFiringSequenceSelfCover_of_largeSequences
      (largeSequencesProduceFiringSequenceSelfCover_of_noPredecessorBound
        hObligations.large_covered_prefix_cut_no_predecessor_bound))
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSound
    exact
      (sound_iff_live_and_bounded_shortCircuit_of_original_bounded
        (original_bounded_of_sound_and_woflan_obligations
          hObligations hSound)).1 hSound
  · intro hLiveBounded
    exact live_and_bounded_shortCircuit_implies_sound
      hLiveBounded.1 hLiveBounded.2

end Petri
end Pm4Lean
