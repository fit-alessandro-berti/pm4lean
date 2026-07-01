import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Large.Sample

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_arbitrarilyLargeNoPredecessorSample
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · exact arbitrarilyLargeCoveredPrefixCutNoPredecessorSample_of_not_length_normalized_cover
  · intro hLarge hCover
    have hBound : HasLargeCoveredPrefixCutNoPredecessorBound W :=
      hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisCover
        (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized
          hCover)
    obtain ⟨k, hBounded⟩ := hBound
    obtain ⟨ts, Mend, hSeq, samples, hCovered, sample, hSampleMem,
      hNoPredecessor, p, hLargeSample⟩ := hLarge k
    exact Nat.not_lt_of_ge
      (hBounded ts Mend hSeq samples hCovered sample hSampleMem
        hNoPredecessor p)
      hLargeSample

end Petri
end Pm4Lean
