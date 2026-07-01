import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.FiniteBound.NoPredecessorObligations

namespace Pm4Lean
namespace Petri

theorem no_predecessor_greedy_coordinate_finite_bound_basis_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
      W :=
  (woflan_no_predecessor_greedy_coordinate_finite_bound_obligations_of_original_bounded
    hBounded).large_covered_prefix_cut_no_predecessor_greedy_coordinate_finite_bound_basis

theorem original_bounded_of_sound_and_no_predecessor_greedy_coordinate_finite_bound_basis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_finiteBoundBasis
      hBasis)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_no_predecessor_greedy_coordinate_finite_bound_basis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_noPredecessorGreedy_finiteBoundBasis
      hBasis)

theorem original_bounded_iff_no_predecessor_greedy_coordinate_finite_bound_basis_of_sound
    {W : WFNet}
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W := by
  constructor
  · exact no_predecessor_greedy_coordinate_finite_bound_basis_of_original_bounded
  · intro hBasis
    exact
      original_bounded_of_sound_and_no_predecessor_greedy_coordinate_finite_bound_basis
        hBasis hSound

end Petri
end Pm4Lean
