import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Sufficient.Bound.FromCoordinate

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_bound
    {W : WFNet} {k : Nat}
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W k) :
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
      W k := by
  intro ts Mend hSeq samples hSamplesCovered coords hCoordsMem x hXMem
  obtain ⟨sample, hSampleMem, hNoPredecessor, p, hEq⟩ :=
    FiringSequence.exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem
  simpa [hEq] using
    hBounded ts Mend hSeq samples hSamplesCovered sample
      hSampleMem hNoPredecessor p

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound
    {W : WFNet}
    (hBound :
      HasLargeCoveredPrefixCutNoPredecessorBound W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact ⟨k,
    largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_of_bound
      hBounded⟩

end Petri
end Pm4Lean
