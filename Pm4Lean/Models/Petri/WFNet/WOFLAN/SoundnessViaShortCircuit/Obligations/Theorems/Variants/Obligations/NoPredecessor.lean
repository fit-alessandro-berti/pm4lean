import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Obligations.Coordinate

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_no_predecessor_greedy_coordinate_obligations
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_no_predecessor_greedy_coordinate_obligations
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy hObligations)

theorem woflan_no_predecessor_greedy_coordinate_obligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  woflanNoPredecessorGreedyCoordinateProofObligations_of_woflan
    (woflanProofObligations_of_original_bounded hBounded)

theorem original_bounded_iff_woflan_no_predecessor_greedy_coordinate_obligations_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      WoflanNoPredecessorGreedyCoordinateProofObligations W := by
  constructor
  · exact
      woflan_no_predecessor_greedy_coordinate_obligations_of_original_bounded
  · intro hObligations
    exact
      original_bounded_of_sound_and_woflan_no_predecessor_greedy_coordinate_obligations
        hObligations hSound

end Petri
end Pm4Lean
