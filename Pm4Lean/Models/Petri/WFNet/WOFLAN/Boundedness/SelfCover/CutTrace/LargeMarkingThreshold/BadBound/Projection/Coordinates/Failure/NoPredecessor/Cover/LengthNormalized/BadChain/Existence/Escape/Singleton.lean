import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Construction

namespace Pm4Lean
namespace Petri

theorem exists_singleton_bound_escape_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (bound : List Nat) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo bound.length (NatListMax bound)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords [bound] := by
  obtain ⟨coordinates, hLengthEq, hChain⟩ :=
    exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
      hNotCover
      ((NatListsUpTo bound.length (NatListMax bound)).length + 1)
  have hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length := by
    simp [hLengthEq]
  exact ⟨coordinates, hChain, hLength,
    exists_not_natListDominatedBy_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
      hChain hLength⟩

theorem exists_singleton_bound_greaterWitness_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    {bound : List Nat}
    (hBoundLength : bound.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo bound.length (NatListMax bound)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          NatListBasisHasGreaterCoordinateWitness coords [bound] := by
  obtain ⟨coordinates, hLengthEq, hChain⟩ :=
    exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
      hNotCover
      ((NatListsUpTo bound.length (NatListMax bound)).length + 1)
  have hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length := by
    simp [hLengthEq]
  exact ⟨coordinates, hChain, hLength,
    exists_basisGreaterCoordinateWitness_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
      hChain hBoundLength hLength⟩

end Petri
end Pm4Lean
