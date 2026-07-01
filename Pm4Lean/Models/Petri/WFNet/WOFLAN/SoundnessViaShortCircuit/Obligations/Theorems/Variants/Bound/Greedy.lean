import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Public

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_greedy_coordinate_bound_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateBoundProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_greedy_bound hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_greedy_coordinate_bound_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateBoundProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_greedy_bound hObligations)

end Petri
end Pm4Lean
