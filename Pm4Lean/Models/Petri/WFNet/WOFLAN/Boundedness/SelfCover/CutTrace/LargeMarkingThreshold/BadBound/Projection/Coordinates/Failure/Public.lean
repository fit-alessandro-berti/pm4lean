import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutNoPredecessorBound_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample W := by
  constructor
  · intro hNotBound k
    exact exists_large_noPredecessorSample_of_not_noPredecessorGreedyBound
      (fun hGreedy =>
        hNotBound
          ((hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateBasisBound).2
            hGreedy))
      k
  · intro hLarge hBound
    obtain ⟨k, hBounded⟩ := hBound
    obtain ⟨ts, Mend, hSeq, samples, hCovered, sample, hSampleMem,
      hNoPredecessor, p, hLt⟩ := hLarge k
    exact Nat.not_lt_of_ge
      (hBounded ts Mend hSeq samples hCovered sample hSampleMem
        hNoPredecessor p)
      hLt

theorem exists_large_noPredecessorSample_of_not_bound
    {W : WFNet}
    (hNotBound : ¬ HasLargeCoveredPrefixCutNoPredecessorBound W)
    (k : Nat) :
    LargeCoveredPrefixCutNoPredecessorSampleAbove W k :=
  (not_hasLargeCoveredPrefixCutNoPredecessorBound_iff.mp hNotBound) k

theorem exists_noPredecessorSample_above_bounds_of_not_bound
    {W : WFNet}
    (hNotBound : ¬ HasLargeCoveredPrefixCutNoPredecessorBound W)
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
  exists_noPredecessorSample_above_bounds_of_not_noPredecessorGreedyFiniteBound
    (fun hFinite =>
      hNotBound
        ((hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateFiniteBoundBasis).2
          hFinite))
    bounds

end Petri
end Pm4Lean
