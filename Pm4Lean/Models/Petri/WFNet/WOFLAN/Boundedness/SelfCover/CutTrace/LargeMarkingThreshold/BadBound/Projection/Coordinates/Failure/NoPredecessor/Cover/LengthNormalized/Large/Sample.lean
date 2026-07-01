import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Large.Greedy

namespace Pm4Lean
namespace Petri

theorem exists_large_noPredecessorSample_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k := by
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, x, hXMem, hLarge⟩ :=
    exists_large_retained_noPredecessorGreedyCoordinate_of_not_length_normalized_cover
      hNotCover k
  obtain ⟨sample, hSampleMem, hNoPredecessor, p, hValueEq⟩ :=
    FiringSequence.exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    sample, hSampleMem, hNoPredecessor, p, by
      simpa [hValueEq] using hLarge⟩

theorem arbitrarilyLargeCoveredPrefixCutNoPredecessorSample_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  intro k
  exact exists_large_noPredecessorSample_of_not_length_normalized_cover
    hNotCover k

end Petri
end Pm4Lean
