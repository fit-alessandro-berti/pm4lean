import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Base.Witness.Greater

namespace Pm4Lean
namespace Petri

theorem exists_retained_noPredecessorGreedyCoordinate_extension_of_not_length_normalized_cover
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
                  upper.length = W.net.places.length) := by
  obtain ⟨ts, Mend, hSeq, samples, hCovered,
      coords, hCoordsMem, hNotDominatedCoords⟩ :=
    exists_retained_noPredecessorGreedyCoordinate_not_dominated_of_not_length_normalized_cover
      hNotCover coordinates hCoordinatesLength
  have hCoordsLength : coords.length = W.net.places.length :=
    FiringSequence.greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
      hCoordsMem
  exact ⟨ts, Mend, hSeq, samples, hCovered,
    coords, hCoordsMem, hCoordsLength,
    not_mem_of_not_natListDominatedBy hNotDominatedCoords,
    hNotDominatedCoords,
    natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
      hCoordsLength
      hCoordinatesLength
      hNotDominatedCoords,
    by
      intro upper hUpperMem
      cases hUpperMem with
      | head =>
          exact hCoordsLength
      | tail _ hTail =>
          exact hCoordinatesLength upper hTail⟩

end Petri
end Pm4Lean
