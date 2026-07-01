import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.FiniteBound.FromFinite

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_iff_finiteBoundBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_basisCover,
    hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_finiteBoundBasis⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_finiteBoundBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_length_normalized,
    hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_finiteBoundBasis⟩

end Petri
end Pm4Lean
