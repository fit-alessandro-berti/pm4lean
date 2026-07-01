import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.Greedy.Bound.BoundedBy

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W ↔
      ∀ k : Nat,
        ∃ ts : List W.net.Transition,
          ∃ Mend : W.Marking,
            ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
              ∃ samples :
                List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
                FiringSequence.PrefixCutsCoveredBySamples samples ∧
                  ∃ coords : List Nat,
                    coords ∈ natListGreedyBasis
                      (FiringSequence.prefixCutSampleCoordinateLists samples) ∧
                      ∃ x : Nat, x ∈ coords ∧ k < x := by
  classical
  simp [HasLargeCoveredPrefixCutGreedyCoordinateBasisBound,
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy, Nat.not_le]

theorem exists_large_retained_greedyCoordinate_of_not_bound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W)
    (k : Nat) :
    ∃ ts : List W.net.Transition,
      ∃ Mend : W.Marking,
        ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
          ∃ samples :
            List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
            FiringSequence.PrefixCutsCoveredBySamples samples ∧
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutSampleCoordinateLists samples) ∧
                  ∃ x : Nat, x ∈ coords ∧ k < x :=
  (not_hasLargeCoveredPrefixCutGreedyCoordinateBasisBound_iff.mp
    hNotBound) k

end Petri
end Pm4Lean
