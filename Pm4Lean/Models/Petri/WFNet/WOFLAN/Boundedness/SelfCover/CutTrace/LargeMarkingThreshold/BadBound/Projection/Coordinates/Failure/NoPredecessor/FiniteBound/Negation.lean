import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Bound

namespace Pm4Lean
namespace Petri

theorem not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_iff
    {W : WFNet} :
    ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis W ↔
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
  rw [← hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_iff_finiteBasis]
  exact
    not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_iff

end Petri
end Pm4Lean
