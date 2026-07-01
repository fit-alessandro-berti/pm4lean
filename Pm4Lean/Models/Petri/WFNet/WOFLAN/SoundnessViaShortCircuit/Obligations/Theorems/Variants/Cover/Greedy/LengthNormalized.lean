import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Cover.Greedy.NoPredecessor

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_no_predecessor_greedy_coordinate_length_normalized_basis_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_lengthNormalizedBasisCover
      hCover)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_no_predecessor_greedy_coordinate_length_normalized_basis_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_lengthNormalizedBasisCover
      hCover)

theorem original_bounded_iff_no_predecessor_greedy_coordinate_length_normalized_basis_cover_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W := by
  constructor
  · exact
      noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_original_bounded
  · intro hCover
    exact
      original_bounded_of_sound_and_no_predecessor_greedy_coordinate_length_normalized_basis_cover
        hCover hSound

end Petri
end Pm4Lean
