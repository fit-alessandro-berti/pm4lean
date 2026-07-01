import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Bridge
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyFiniteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisBound
    (hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_finiteBasis
      hBasis)

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyFiniteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisCover
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_finiteBoundBasis
      hBasis)

end Petri
end Pm4Lean
