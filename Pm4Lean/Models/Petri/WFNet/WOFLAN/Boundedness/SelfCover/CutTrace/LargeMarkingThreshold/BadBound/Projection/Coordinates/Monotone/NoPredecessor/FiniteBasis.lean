import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone.NoPredecessor.Bounds

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_finiteBasis
    {W : WFNet} {bounds : List Nat}
    (hBasis :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome
        W bounds) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W (NatListMax bounds) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  obtain ⟨k, hMem, hBounded⟩ :=
    hBasis ts Mend hSeq samples hSamplesCovered
  exact Nat.le_trans
    (hBounded coords hCoordsMem x hXMem)
    (le_natListMax_of_mem hMem)

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome_singleton
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome
      W [k] := by
  intro ts Mend hSeq samples hSamplesCovered
  exact ⟨k, by simp,
    hBounded ts Mend hSeq samples hSamplesCovered⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_finiteBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W := by
  obtain ⟨bounds, hBounds⟩ := hBasis
  exact ⟨NatListMax bounds,
    largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_finiteBasis
      hBounds⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
      W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact ⟨[k],
    largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome_singleton
      hBounded⟩

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_iff_finiteBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_bound,
    hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_finiteBasis⟩

end Petri
end Pm4Lean
