import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.Bound

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_bound
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_basisCover
      hCover)

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_length_normalized
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_basisCover
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized
      hCover)

end Petri
end Pm4Lean
