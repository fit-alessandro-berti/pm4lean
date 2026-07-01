import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Public

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_coordinate_obligations
    {W : WFNet}
    (hObligations : WoflanCoordinateProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_coordinate hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_coordinate_obligations
    {W : WFNet}
    (hObligations : WoflanCoordinateProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_coordinate hObligations)

theorem woflan_coordinate_obligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanCoordinateProofObligations W :=
  (woflanProofObligations_iff_coordinate).mp
    (woflanProofObligations_of_original_bounded hBounded)

theorem original_bounded_iff_woflan_coordinate_obligations_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      WoflanCoordinateProofObligations W := by
  constructor
  · exact woflan_coordinate_obligations_of_original_bounded
  · intro hObligations
    exact
      original_bounded_of_sound_and_woflan_coordinate_obligations
        hObligations hSound

theorem original_bounded_of_sound_and_woflan_greedy_coordinate_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_greedy hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_greedy_coordinate_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_greedy hObligations)

end Petri
end Pm4Lean
