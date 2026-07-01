import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone.Greedy.BoundedBy

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_of_finiteBasis
    {W : WFNet} {bounds : List Nat}
    (hBasis :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome W bounds) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy
      W (NatListMax bounds) := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  obtain ⟨k, hMem, hBounded⟩ :=
    hBasis ts Mend hSeq samples hSamplesCovered
  exact Nat.le_trans
    (hBounded coords hCoordsMem x hXMem)
    (le_natListMax_of_mem hMem)

theorem largeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome_singleton
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome W [k] := by
  intro ts Mend hSeq samples hSamplesCovered
  exact ⟨k, by simp, hBounded ts Mend hSeq samples hSamplesCovered⟩

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_finiteBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W := by
  obtain ⟨bounds, hBounds⟩ := hBasis
  exact ⟨NatListMax bounds,
    largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_of_finiteBasis
      hBounds⟩

theorem hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W) :
    HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact ⟨[k],
    largeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome_singleton
      hBounded⟩

theorem hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_iff_finiteBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W ↔
      HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W :=
  ⟨hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_of_bound,
    hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_of_finiteBasis⟩

end Petri
end Pm4Lean
