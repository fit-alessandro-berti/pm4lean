import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Base.Negation

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (coordinates : List (List Nat))
    (hCoordinatesLength :
      ∀ upper : List Nat, upper ∈ coordinates →
        upper.length = W.net.places.length) :
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
  (not_hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_iff.mp
    hNotCover) coordinates hCoordinatesLength

end Petri
end Pm4Lean
