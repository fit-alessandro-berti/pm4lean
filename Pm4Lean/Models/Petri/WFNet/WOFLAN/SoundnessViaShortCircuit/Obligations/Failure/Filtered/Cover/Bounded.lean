import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.Witness

namespace Pm4Lean
namespace Petri

theorem arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W) :
    ArbitrarilyLargeFiringSequenceMarking W :=
  arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    (not_woflanNoPredecessorGreedyCoordinateProofObligations_iff.mp
      hNotObligations)

theorem not_original_bounded_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W) :
    ¬ TokenBoundedReachableOriginal W :=
  not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
    (arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
      hNotObligations)

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  woflanNoPredecessorGreedyCoordinateProofObligations_of_woflan
    (woflanProofObligations_of_original_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  woflanNoPredecessorGreedyCoordinateProofObligations_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_live_and_bounded_shortCircuit
    {W : WFNet}
    (hLiveBounded :
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  woflanNoPredecessorGreedyCoordinateProofObligations_of_shortCircuit_bounded
    hLiveBounded.2

end Petri
end Pm4Lean
