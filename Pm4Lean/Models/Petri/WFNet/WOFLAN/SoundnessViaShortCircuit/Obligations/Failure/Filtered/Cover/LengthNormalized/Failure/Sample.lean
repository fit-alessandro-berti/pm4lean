import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public

namespace Pm4Lean
namespace Petri

theorem not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_arbitrarilyLargeNoPredecessorSample
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  exact
    not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_arbitrarilyLargeNoPredecessorSample

theorem exists_large_noPredecessorSample_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff_arbitrarilyLargeNoPredecessorSample.mp
    hNotCover) k

end Petri
end Pm4Lean
