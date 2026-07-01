import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain

namespace Pm4Lean
namespace Petri

theorem exists_large_retained_noPredecessorGreedyCoordinate_of_not_length_normalized_cover
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
                ∃ x : Nat, x ∈ coords ∧ k < x := by
  classical
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, hNotDominated⟩ :=
    exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_length_normalized_cover
      hNotCover
      (NatListsUpTo W.net.places.length k)
      (fun upper hUpperMem => length_eq_of_mem_natListsUpTo hUpperMem)
  refine ⟨ts, Mend, hSeq, samples, hCovered, coords, hCoordsMem, ?_⟩
  by_cases hLarge : ∃ x : Nat, x ∈ coords ∧ k < x
  · exact hLarge
  · have hBound : ∀ x : Nat, x ∈ coords → x ≤ k := by
      intro x hXMem
      by_cases hLe : x ≤ k
      · exact hLe
      · exact False.elim
          (hLarge ⟨x, hXMem, Nat.lt_of_not_ge hLe⟩)
    exact False.elim
      (hNotDominated
        (natListDominatedBy_of_mem
          (mem_natListsUpTo
            (FiringSequence.greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
              hCoordsMem)
            hBound)))

end Petri
end Pm4Lean
