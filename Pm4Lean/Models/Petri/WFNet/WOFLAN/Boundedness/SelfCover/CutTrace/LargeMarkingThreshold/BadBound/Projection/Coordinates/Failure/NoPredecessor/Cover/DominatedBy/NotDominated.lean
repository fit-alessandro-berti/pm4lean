import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.DominatedBy.Negation

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_dominatedBy
    {W : WFNet} {coordinates : List (List Nat)}
    (hNotDominated :
      ¬ LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates) :
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
                  ¬ NatListDominatedBy coords coordinates :=
  not_largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy_iff.mp
    hNotDominated

end Petri
end Pm4Lean
