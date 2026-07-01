import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.FiniteBound.Large

namespace Pm4Lean
namespace Petri

theorem arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W) :
    ArbitrarilyLargeFiringSequenceMarking W :=
  arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    (not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_iff.mp
      hNotObligations)

theorem not_original_bounded_of_not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W) :
    ¬ TokenBoundedReachableOriginal W :=
  not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
    (arbitrarilyLargeFiringSequenceMarking_of_not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
      hNotObligations)

end Petri
end Pm4Lean
