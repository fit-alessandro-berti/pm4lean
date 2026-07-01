import Pm4Lean.Models.Petri.Behavior.Liveness
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Original
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure

namespace Pm4Lean
namespace Petri

theorem not_woflanProofObligations_iff
    {W : WFNet} :
    ¬ WoflanProofObligations W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · intro hNotObligations
    exact
      not_hasLargeCoveredPrefixCutNoPredecessorBound_iff.mp
        (fun hBound => hNotObligations ⟨hBound⟩)
  · intro hLarge hObligations
    exact
      (not_hasLargeCoveredPrefixCutNoPredecessorBound_iff.mpr hLarge)
        hObligations.large_covered_prefix_cut_no_predecessor_bound

theorem exists_large_noPredecessorSample_of_not_woflanProofObligations
    {W : WFNet}
    (hNotObligations : ¬ WoflanProofObligations W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_woflanProofObligations_iff.mp hNotObligations) k

theorem exists_noPredecessorSample_above_bounds_of_not_woflanProofObligations
    {W : WFNet}
    (hNotObligations : ¬ WoflanProofObligations W)
    (bounds : List Nat) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ sample :
                FiringSequence.PrefixCutSample W.net W.initial ts Mend,
                sample ∈ samples ∧
                  ¬ FiringSequence.HasComparablePrefixCutPredecessor
                    sample ∧
                  ∃ p : W.net.Place,
                    ∀ k : Nat, k ∈ bounds → k < sample.marking p :=
  exists_noPredecessorSample_above_bounds_of_not_bound
    (fun hBound => hNotObligations ⟨hBound⟩)
    bounds

theorem arbitrarilyLargeFiringSequenceMarking_of_not_woflanProofObligations
    {W : WFNet}
    (hNotObligations : ¬ WoflanProofObligations W) :
    ArbitrarilyLargeFiringSequenceMarking W :=
  arbitrarilyLargeFiringSequenceMarking_of_arbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    (not_woflanProofObligations_iff.mp hNotObligations)

theorem not_original_bounded_of_not_woflanProofObligations
    {W : WFNet}
    (hNotObligations : ¬ WoflanProofObligations W) :
    ¬ TokenBoundedReachableOriginal W :=
  not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
    (arbitrarilyLargeFiringSequenceMarking_of_not_woflanProofObligations
      hNotObligations)

end Petri
end Pm4Lean
