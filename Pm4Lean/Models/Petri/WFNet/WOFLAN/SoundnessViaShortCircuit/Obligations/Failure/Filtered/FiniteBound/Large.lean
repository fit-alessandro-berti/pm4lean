import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public

namespace Pm4Lean
namespace Petri

theorem not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_iff
    {W : WFNet} :
    ¬ WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · intro hNotObligations
    exact not_woflanProofObligations_iff.mp
      (fun hWoflan =>
        hNotObligations
          ((woflanProofObligations_iff_noPredecessorGreedyCoordinateFiniteBound).1
            hWoflan))
  · intro hLarge hObligations
    exact
      (not_woflanProofObligations_iff.mpr hLarge)
        ((woflanProofObligations_iff_noPredecessorGreedyCoordinateFiniteBound).2
          hObligations)

theorem exists_large_noPredecessorSample_of_not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_iff.mp
    hNotObligations) k

theorem exists_noPredecessorSample_above_bounds_of_not_woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
    {W : WFNet}
    (hNotObligations :
      ¬ WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W)
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
                    ∀ k : Nat, k ∈ bounds → k < sample.marking p := by
  exact
    exists_noPredecessorSample_above_bounds_of_not_noPredecessorGreedyFiniteBound
      (fun hBasis =>
        hNotObligations
          ⟨hBasis⟩)
      bounds

end Petri
end Pm4Lean
