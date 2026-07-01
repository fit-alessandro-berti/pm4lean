import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Escape.Singleton

namespace Pm4Lean
namespace Petri

theorem exists_basis_escape_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat))
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords basis := by
  obtain ⟨coordinates, hLengthEq, hChain⟩ :=
    exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
      hNotCover
      ((NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length + 1)
  have hLength :
      (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
        coordinates.length := by
    simp [hLengthEq]
  exact ⟨coordinates, hChain, hLength,
    exists_not_natListDominatedBy_of_lengthNormalizedBadCoverChain_length_gt_basis
      hChain hBasisLength hLength⟩

theorem exists_basis_greaterWitness_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat))
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          NatListBasisHasGreaterCoordinateWitness coords basis := by
  obtain ⟨coordinates, hLengthEq, hChain⟩ :=
    exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
      hNotCover
      ((NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length + 1)
  have hLength :
      (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
        coordinates.length := by
    simp [hLengthEq]
  exact ⟨coordinates, hChain, hLength,
    exists_basisGreaterCoordinateWitness_of_lengthNormalizedBadCoverChain_length_gt_basis
      hChain hBasisLength hLength⟩

end Petri
end Pm4Lean
