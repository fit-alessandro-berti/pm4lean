import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.All.Cover
import Pm4Lean.Util.NatListBox

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutGreedyCoordinateBasesDominatedBy_box_of_boundedBy
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy
      W (NatListsUpTo W.net.places.length k) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem
  exact
    natListDominatedBy_of_mem
      (mem_natListsUpTo
        (FiringSequence.greedyPrefixCutSampleCoordinateBasis_length_of_mem
          hCoordsMem)
        (hBounded ts Mend hSeq samples hSamplesCovered coords hCoordsMem))

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_boundedBy
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W :=
  ⟨NatListsUpTo W.net.places.length k,
    largeCoveredPrefixCutGreedyCoordinateBasesDominatedBy_box_of_boundedBy
      hBounded⟩

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact
    hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_boundedBy
      hBounded

end Petri
end Pm4Lean
