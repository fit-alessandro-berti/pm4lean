import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.Cover
import Pm4Lean.Util.NatListBasis.Transfer

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_filter_placeLength
    {W : WFNet} {coordinates : List (List Nat)}
    (hDominated :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
      W (coordinates.filter
        (fun coords => coords.length = W.net.places.length)) := by
  intro ts Mend hSeq samples hSamplesCovered
  exact natListBasisDominatesAll_filter_length_eq
    (fun coords hMem =>
      FiringSequence.greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
        hMem)
    (hDominated ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_length_normalized
    {W : WFNet}
    (hGreedyCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W := by
  obtain ⟨coordinates, hDominated⟩ := hGreedyCover
  refine ⟨coordinates.filter
    (fun coords => coords.length = W.net.places.length), ?_, ?_⟩
  · intro coords hMem
    exact of_decide_eq_true (List.mem_filter.mp hMem).2
  · exact
      largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_filter_placeLength
        hDominated

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized
    {W : WFNet}
    (hGreedyCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W := by
  obtain ⟨coordinates, _hLength, hDominated⟩ := hGreedyCover
  exact ⟨coordinates, hDominated⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_iff_length_normalized
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_length_normalized,
    hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized⟩

end Petri
end Pm4Lean
