import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.FiniteBound.ToFinite

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_finiteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_finiteBasis
      hBasis)

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_finiteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_length_normalized
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_finiteBoundBasis
      hBasis)

end Petri
end Pm4Lean
