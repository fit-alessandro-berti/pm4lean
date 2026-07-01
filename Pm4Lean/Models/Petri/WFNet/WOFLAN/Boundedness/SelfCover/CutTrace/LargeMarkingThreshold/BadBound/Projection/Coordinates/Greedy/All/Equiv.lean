import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Greedy.All.Box

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_of_dominatedBy
    {W : WFNet} {coordinates : List (List Nat)}
    (hDominated :
      LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy W coordinates) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy
      W (NatListMax (coordinates.map NatListMax)) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  obtain ⟨upper, hUpperMem, hLe⟩ :=
    hDominated ts Mend hSeq samples hSamplesCovered coords hCoordsMem
  exact Nat.le_trans
    (forall_le_natListMax_of_natListLe hLe x hXMem)
    (le_natListMax_of_mem
      (List.mem_map.mpr ⟨upper, hUpperMem, rfl⟩))

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W := by
  obtain ⟨coordinates, hDominated⟩ := hCover
  exact ⟨NatListMax (coordinates.map NatListMax),
    largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_of_dominatedBy
      hDominated⟩

theorem hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W :=
  hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_of_bound
    (hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_basisCover hCover)

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_iff_finiteBoundBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W ↔
      HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W :=
  ⟨hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_of_basisCover,
    fun hBasis =>
      hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_bound
        (hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_finiteBasis
          hBasis)⟩

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisBound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisCover
    (hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_bound hBound)

end Petri
end Pm4Lean
