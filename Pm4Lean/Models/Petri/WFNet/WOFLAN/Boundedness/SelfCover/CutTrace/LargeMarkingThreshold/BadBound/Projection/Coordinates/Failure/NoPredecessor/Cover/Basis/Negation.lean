import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.DominatedBy

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W ↔
      ∀ coordinates : List (List Nat),
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
  simp [HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover,
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy,
    NatListBasisDominatesAll]

end Petri
end Pm4Lean
