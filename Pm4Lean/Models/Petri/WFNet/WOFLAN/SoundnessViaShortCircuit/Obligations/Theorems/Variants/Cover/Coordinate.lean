import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Cover.Marking

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_no_predecessor_coordinate_dominating_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    ⟨hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
      hCover⟩
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_no_predecessor_coordinate_dominating_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    ⟨hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
      hCover⟩

theorem original_bounded_iff_no_predecessor_coordinate_dominating_cover_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W := by
  constructor
  · intro hBounded
    exact
      hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_bound
        (woflanProofObligations_of_original_bounded
          hBounded).large_covered_prefix_cut_no_predecessor_bound
  · intro hCover
    exact
      original_bounded_of_sound_and_no_predecessor_coordinate_dominating_cover
        hCover hSound

end Petri
end Pm4Lean
