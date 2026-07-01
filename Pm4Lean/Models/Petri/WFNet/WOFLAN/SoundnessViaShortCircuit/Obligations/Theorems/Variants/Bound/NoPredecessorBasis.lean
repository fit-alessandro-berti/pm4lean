import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Bound.NoPredecessorObligations

namespace Pm4Lean
namespace Petri

theorem no_predecessor_greedy_coordinate_basis_bound_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W :=
  (woflan_no_predecessor_greedy_coordinate_bound_obligations_of_original_bounded
    hBounded).large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_bound

theorem original_bounded_iff_no_predecessor_greedy_coordinate_basis_bound_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W := by
  constructor
  · exact no_predecessor_greedy_coordinate_basis_bound_of_original_bounded
  · intro hBound
    exact
      original_bounded_of_sound_and_woflan_no_predecessor_greedy_coordinate_bound_obligations
        ⟨hBound⟩ hSound

end Petri
end Pm4Lean
