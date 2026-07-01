import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.Greedy.FiniteBound.Large

namespace Pm4Lean
namespace Petri

theorem exists_retained_greedyCoordinate_above_bounds_of_not_finiteBound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W)
    (bounds : List Nat) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutSampleCoordinateLists samples) ∧
                  ∃ x : Nat,
                    x ∈ coords ∧
                      ∀ k : Nat, k ∈ bounds → k < x := by
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, x, hXMem, hLarge⟩ :=
    exists_large_retained_greedyCoordinate_of_not_finiteBound
      hNotBound (NatListMax bounds)
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    coords, hCoordsMem, x, hXMem, by
      intro k hMem
      exact Nat.lt_of_le_of_lt (le_natListMax_of_mem hMem) hLarge⟩

end Petri
end Pm4Lean
