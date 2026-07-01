import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Cover.BadChain

namespace Pm4Lean
namespace Petri

theorem exists_large_retained_noPredecessorGreedyCoordinate_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                    samples) ∧
                ∃ x : Nat, x ∈ coords ∧ k < x :=
  exists_large_retained_noPredecessorGreedyCoordinate_of_not_length_normalized_cover
    hNotCover k

theorem exists_noPredecessorSample_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
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
                  ∃ p : W.net.Place, k < sample.marking p := by
  exact exists_large_noPredecessorSample_of_not_length_normalized_cover
    hNotCover k

end Petri
end Pm4Lean
