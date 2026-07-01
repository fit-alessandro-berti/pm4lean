import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Monotone

namespace Pm4Lean
namespace Petri

theorem not_largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_iff
    {W : WFNet} {k : Nat} :
    ¬ LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k ↔
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
  simp [LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy, Nat.not_le]

theorem exists_large_retained_greedyCoordinate_of_not_boundedBy
    {W : WFNet} {k : Nat}
    (hNotBounded :
      ¬ LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k) :
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
  not_largeCoveredPrefixCutGreedyCoordinateBasesBoundedBy_iff.mp
    hNotBounded

end Petri
end Pm4Lean
