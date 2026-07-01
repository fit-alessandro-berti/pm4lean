import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Sufficient

namespace Pm4Lean
namespace Petri

theorem not_largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_iff
    {W : WFNet} {coordinates : List (List Nat)} :
    ¬ LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates ↔
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
                    ¬ NatListDominatedBy coords coordinates := by
  classical
  simp [LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy,
    NatListBasisDominatesAll]

end Petri
end Pm4Lean
