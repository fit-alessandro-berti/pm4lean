import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.Bound

namespace Pm4Lean
namespace Petri

theorem woflanGreedyCoordinateBoundProofObligations_of_finiteBasis
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanGreedyCoordinateBoundProofObligations W :=
  ⟨hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_finiteBasis
    hObligations.large_covered_prefix_cut_greedy_coordinate_finite_bound_basis⟩

theorem woflanGreedyCoordinateFiniteBoundProofObligations_of_basis
    {W : WFNet}
    (hBasis : HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    WoflanGreedyCoordinateFiniteBoundProofObligations W :=
  ⟨hBasis⟩

theorem woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_finiteBasis
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_finiteBasis
    hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_finite_bound_basis⟩

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_basis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  ⟨hBasis⟩

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_basis
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_basisCover
      hCover)

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_lengthNormalizedBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_basis
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_length_normalized
      hCover)

end Petri
end Pm4Lean
