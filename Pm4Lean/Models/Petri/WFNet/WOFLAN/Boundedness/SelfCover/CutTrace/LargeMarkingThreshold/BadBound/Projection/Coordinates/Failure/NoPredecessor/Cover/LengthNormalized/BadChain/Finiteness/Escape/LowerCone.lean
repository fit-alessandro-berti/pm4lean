import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness.Bounds

namespace Pm4Lean
namespace Petri

theorem exists_not_natListLe_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧ ¬ NatListLe coords bound :=
  exists_not_natListLe_of_not_containsNatListLePair_length_gt_natListLe_bound
    (not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain)
    hLength

theorem exists_not_natListDominatedBy_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      ¬ NatListDominatedBy coords [bound] :=
  exists_not_natListDominatedBy_singleton_of_not_containsNatListLePair_length_gt_natListLe_bound
    (not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain)
    hLength

theorem exists_natListHasGreaterCoordinate_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBoundLength : bound.length = W.net.places.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListHasGreaterCoordinate coords bound := by
  apply exists_natListHasGreaterCoordinate_of_not_containsNatListLePair_length_gt_natListLe_bound
  · exact not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain
  · intro coords hCoordsMem
    rw [hBoundLength]
    exact length_eq_of_mem_lengthNormalizedBadCoverChain hChain coords hCoordsMem
  · exact hLength

theorem exists_basisGreaterCoordinateWitness_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBoundLength : bound.length = W.net.places.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListBasisHasGreaterCoordinateWitness coords [bound] := by
  apply exists_basisGreaterCoordinateWitness_singleton_of_not_containsNatListLePair_length_gt_natListLe_bound
  · exact not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain
  · intro coords hCoordsMem
    rw [hBoundLength]
    exact length_eq_of_mem_lengthNormalizedBadCoverChain hChain coords hCoordsMem
  · exact hLength

end Petri
end Pm4Lean
