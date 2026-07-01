import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Bound.Greedy

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_no_predecessor_greedy_coordinate_bound_obligations
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_bound hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_no_predecessor_greedy_coordinate_bound_obligations
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_bound hObligations)

theorem woflan_no_predecessor_greedy_coordinate_bound_obligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  (woflanProofObligations_iff_noPredecessorGreedyCoordinateBound).mp
    (woflanProofObligations_of_original_bounded hBounded)

theorem original_bounded_iff_woflan_no_predecessor_greedy_coordinate_bound_obligations_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W := by
  constructor
  · exact
      woflan_no_predecessor_greedy_coordinate_bound_obligations_of_original_bounded
  · intro hObligations
    exact
      original_bounded_of_sound_and_woflan_no_predecessor_greedy_coordinate_bound_obligations
        hObligations hSound

end Petri
end Pm4Lean
