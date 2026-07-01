import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_noPredecessorGreedy_dominated
    {W : WFNet} {coordinates : List (List Nat)}
    (hGreedyDominated :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W coordinates := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_noPredecessorGreedy_dominated
      (hGreedyDominated ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedy_dominated
    {W : WFNet} {coordinates : List (List Nat)}
    (hGreedyDominated :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  ⟨coordinates,
    largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_noPredecessorGreedy_dominated
      hGreedyDominated⟩

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisCover
    {W : WFNet}
    (hGreedyCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W := by
  obtain ⟨coordinates, hGreedyDominated⟩ := hGreedyCover
  exact
    hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedy_dominated
      hGreedyDominated

end Petri
end Pm4Lean
