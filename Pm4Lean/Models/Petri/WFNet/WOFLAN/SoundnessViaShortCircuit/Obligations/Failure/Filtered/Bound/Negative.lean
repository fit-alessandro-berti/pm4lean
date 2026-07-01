import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public

namespace Pm4Lean
namespace Petri

theorem not_woflanNoPredecessorGreedyCoordinateBoundProofObligations_iff
    {W : WFNet} :
    ¬ WoflanNoPredecessorGreedyCoordinateBoundProofObligations W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · intro hNotObligations
    exact not_woflanProofObligations_iff.mp
      (fun hWoflan =>
        hNotObligations
          ((woflanProofObligations_iff_noPredecessorGreedyCoordinateBound).1
            hWoflan))
  · intro hLarge hObligations
    exact
      (not_woflanProofObligations_iff.mpr hLarge)
        ((woflanProofObligations_iff_noPredecessorGreedyCoordinateBound).2
          hObligations)

theorem exists_large_noPredecessorSample_of_not_woflanNoPredecessorGreedyCoordinateBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateBoundProofObligations W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_woflanNoPredecessorGreedyCoordinateBoundProofObligations_iff.mp
    hNotObligations) k

theorem arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    ArbitrarilyLargeFiringSequenceMarking W :=
  arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    (not_woflanNoPredecessorGreedyCoordinateBoundProofObligations_iff.mp
      hNotObligations)

theorem not_original_bounded_of_not_woflanNoPredecessorGreedyCoordinateBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    ¬ TokenBoundedReachableOriginal W :=
  not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
    (arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateBoundProofObligations
      hNotObligations)

end Petri
end Pm4Lean
