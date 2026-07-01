import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Equiv.Records

namespace Pm4Lean
namespace Petri

theorem woflanProofObligations_iff_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet} :
    WoflanProofObligations W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W :=
  ⟨fun hObligations =>
      (hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateLengthNormalizedBasisCover).1
        hObligations.large_covered_prefix_cut_no_predecessor_bound,
    fun hCover =>
      ⟨(hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateLengthNormalizedBasisCover).2
        hCover⟩⟩

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_finiteBoundObligations
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W ↔
      WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  ⟨woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_lengthNormalizedBasisCover,
    fun hObligations =>
      hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_finiteBoundBasis
        hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_finite_bound_basis⟩

end Petri
end Pm4Lean
