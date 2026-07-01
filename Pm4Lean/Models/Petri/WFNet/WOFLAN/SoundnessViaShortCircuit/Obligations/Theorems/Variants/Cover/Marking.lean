import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Public

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_no_predecessor_marking_dominating_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    ⟨hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
      hCover⟩
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_no_predecessor_marking_dominating_cover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    ⟨hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
      hCover⟩

theorem original_bounded_iff_no_predecessor_marking_dominating_cover_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W := by
  constructor
  · intro hBounded
    exact
      hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_bound
        (woflanProofObligations_of_original_bounded
          hBounded).large_covered_prefix_cut_no_predecessor_bound
  · intro hCover
    exact
      original_bounded_of_sound_and_no_predecessor_marking_dominating_cover
        hCover hSound

end Petri
end Pm4Lean
