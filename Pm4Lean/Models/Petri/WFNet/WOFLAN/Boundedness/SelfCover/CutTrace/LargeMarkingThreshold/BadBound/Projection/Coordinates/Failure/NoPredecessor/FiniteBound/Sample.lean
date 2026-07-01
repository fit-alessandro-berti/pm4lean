import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.FiniteBound.Coordinate

namespace Pm4Lean
namespace Petri

theorem exists_noPredecessorSample_above_bounds_of_not_noPredecessorGreedyFiniteBound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W)
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
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, x, hXMem, hLarge⟩ :=
    exists_retained_noPredecessorGreedyCoordinate_above_bounds_of_not_finiteBound
      hNotBound bounds
  obtain ⟨sample, hSampleMem, hNoPredecessor, p, hValueEq⟩ :=
    FiringSequence.exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    sample, hSampleMem, hNoPredecessor, p, by
      intro k hMem
      simpa [hValueEq] using hLarge k hMem⟩

theorem exists_large_noPredecessorSample_of_not_noPredecessorGreedyFiniteBound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
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
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, x, hXMem, hLarge⟩ :=
    exists_large_retained_noPredecessorGreedyCoordinate_of_not_finiteBound
      hNotBound k
  obtain ⟨sample, hSampleMem, hNoPredecessor, p, hValueEq⟩ :=
    FiringSequence.exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    sample, hSampleMem, hNoPredecessor, p, by simpa [hValueEq] using hLarge⟩

end Petri
end Pm4Lean
