import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.Greedy.FiniteBound.Negation

namespace Pm4Lean
namespace Petri

theorem exists_large_retained_greedyCoordinate_of_not_finiteBound
    {W : WFNet}
    (hNotBound :
      ¬ HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W)
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
  (not_hasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis_iff.mp
    hNotBound) k

end Petri
end Pm4Lean
