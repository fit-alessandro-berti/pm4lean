import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Failure.Extension.GreaterWitness

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_extension_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
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
                coords.length = W.net.places.length ∧
                coords ∉ coordinates ∧
                ¬ NatListDominatedBy coords coordinates ∧
                NatListBasisHasGreaterCoordinateWitness
                  coords coordinates ∧
                (∀ upper : List Nat, upper ∈ coords :: coordinates →
                  upper.length = W.net.places.length) :=
  exists_retained_noPredecessorGreedyCoordinate_extension_of_not_length_normalized_cover
    hNotCover coordinates hCoordinatesLength

end Petri
end Pm4Lean
