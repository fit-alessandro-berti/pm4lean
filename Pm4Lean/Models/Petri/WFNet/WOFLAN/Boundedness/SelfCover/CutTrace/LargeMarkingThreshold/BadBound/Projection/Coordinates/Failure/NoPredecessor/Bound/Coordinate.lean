import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Bound.Negation

namespace Pm4Lean
namespace Petri

theorem exists_large_retained_noPredecessorGreedyCoordinate_of_not_boundedBy
    {W : WFNet} {k : Nat}
    (hNotBounded :
      ¬ LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
        W k) :
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
  not_largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy_iff.mp
    hNotBounded

theorem exists_large_retained_noPredecessorGreedyCoordinate_of_not_bound
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
              ∃ coords : List Nat,
                coords ∈ natListGreedyBasis
                  (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                    samples) ∧
                  ∃ x : Nat, x ∈ coords ∧ k < x :=
  (not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_iff.mp
    hNotBound) k

end Petri
end Pm4Lean
