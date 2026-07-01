import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.NoPredecessor.Bound.ToCover

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_dominatedBy
    {W : WFNet} {coordinates : List (List Nat)}
    (hDominated :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W (NatListMax (coordinates.map NatListMax)) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  obtain ⟨upper, hUpperMem, hLe⟩ :=
    hDominated ts Mend hSeq samples hSamplesCovered coords hCoordsMem
  exact Nat.le_trans
    (forall_le_natListMax_of_natListLe hLe x hXMem)
    (le_natListMax_of_mem
      (List.mem_map.mpr ⟨upper, hUpperMem, rfl⟩))

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W := by
  obtain ⟨coordinates, hDominated⟩ := hCover
  exact ⟨NatListMax (coordinates.map NatListMax),
    largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_dominatedBy
      hDominated⟩

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisBound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisCover
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
      hBound)

end Petri
end Pm4Lean
