import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Cover.Large

namespace Pm4Lean
namespace Petri

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  Classical.byContradiction (fun hNotCover =>
    not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
      (arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
        (not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_arbitrarilyLargeNoPredecessorSample.mp
          hNotCover))
      hBounded)

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_live_and_bounded_shortCircuit
    {W : WFNet}
    (hLiveBounded :
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_shortCircuit_bounded
    hLiveBounded.2

end Petri
end Pm4Lean
