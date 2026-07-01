import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Sufficient

namespace Pm4Lean
namespace Petri

theorem not_largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_iff
    {W : WFNet} {k : Nat} :
    ¬ LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
        W k ↔
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
  simp [LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy,
    Nat.not_le]

theorem not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W ↔
      ∀ k : Nat,
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
  simp [HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound,
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy,
    Nat.not_le]

end Petri
end Pm4Lean
