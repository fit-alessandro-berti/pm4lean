import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Bound.Coordinate

namespace Pm4Lean
namespace Petri

theorem exists_large_noPredecessorSample_of_not_noPredecessorGreedyBound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W)
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
    exists_large_retained_noPredecessorGreedyCoordinate_of_not_bound
      hNotBound k
  obtain ⟨sample, hSampleMem, hNoPredecessor, p, hValueEq⟩ :=
    FiringSequence.exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    sample, hSampleMem, hNoPredecessor, p, by simpa [hValueEq] using hLarge⟩

end Petri
end Pm4Lean
