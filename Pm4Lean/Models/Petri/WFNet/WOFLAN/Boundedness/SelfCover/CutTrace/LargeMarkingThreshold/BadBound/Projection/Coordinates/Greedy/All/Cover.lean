import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone.Greedy

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_greedy_dominated
    {W : WFNet} {coordinates : List (List Nat)}
    (hGreedyDominated :
      LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W coordinates := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_greedy_dominated
      (hGreedyDominated ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedy_dominated
    {W : WFNet} {coordinates : List (List Nat)}
    (hGreedyDominated :
      LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy
        W coordinates) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  ⟨coordinates,
    largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_greedy_dominated
      hGreedyDominated⟩

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisCover
    {W : WFNet}
    (hGreedyCover :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W := by
  obtain ⟨coordinates, hGreedyDominated⟩ := hGreedyCover
  exact
    hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedy_dominated
      hGreedyDominated

end Petri
end Pm4Lean
