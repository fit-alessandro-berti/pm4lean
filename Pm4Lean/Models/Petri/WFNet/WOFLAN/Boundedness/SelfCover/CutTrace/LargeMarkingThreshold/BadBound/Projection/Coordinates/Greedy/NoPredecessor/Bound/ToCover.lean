import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.Normalize
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone.NoPredecessor
import Pm4Lean.Util.NatListBox

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_box_of_boundedBy
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
      W (NatListsUpTo W.net.places.length k) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem
  exact
    natListDominatedBy_of_mem
      (mem_natListsUpTo
        (FiringSequence.greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
          hCoordsMem)
        (hBounded ts Mend hSeq samples hSamplesCovered coords hCoordsMem))

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_boundedBy
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W :=
  ⟨NatListsUpTo W.net.places.length k,
    largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_box_of_boundedBy
      hBounded⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_boundedBy
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_length_normalized
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_boundedBy
      hBounded)

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact
    hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_boundedBy
      hBounded

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_length_normalized
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
      hBound)

end Petri
end Pm4Lean
