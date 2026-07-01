import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized

namespace Pm4Lean
namespace Petri

theorem not_woflanNoPredecessorGreedyCoordinateProofObligations_iff
    {W : WFNet} :
    ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · intro hNotObligations
    exact not_woflanProofObligations_iff.mp
      (fun hWoflan =>
        hNotObligations
          ((woflanProofObligations_iff_noPredecessorGreedyCoordinateBasisCover).1
            hWoflan))
  · intro hLarge hObligations
    exact
      (not_woflanProofObligations_iff.mpr hLarge)
        ((woflanProofObligations_iff_noPredecessorGreedyCoordinateBasisCover).2
          hObligations)

theorem exists_large_noPredecessorSample_of_not_woflanNoPredecessorGreedyCoordinateProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateProofObligations W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_woflanNoPredecessorGreedyCoordinateProofObligations_iff.mp
    hNotObligations) k

end Petri
end Pm4Lean
