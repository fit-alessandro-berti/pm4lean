import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Sufficient.Coordinate

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_greedyBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisCover
      hCover)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisCover
      hCover)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_greedyBasisBound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisBound
      hBound)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisBound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisBound
      hBound)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyFiniteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyFiniteBoundBasis
      hBasis)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_greedyFiniteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    (hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyFiniteBoundBasis
      hBasis)

end Petri
end Pm4Lean
