import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Singleton.Bounds

namespace Pm4Lean
namespace Petri

theorem exists_not_natListLe_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧ ¬ NatListLe coords bound :=
  exists_not_natListLe_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    hChain hLength

theorem exists_not_natListDominatedBy_singleton_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      ¬ NatListDominatedBy coords [bound] :=
  exists_not_natListDominatedBy_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    hChain hLength

theorem exists_natListHasGreaterCoordinate_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBoundLength : bound.length = W.net.places.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListHasGreaterCoordinate coords bound :=
  exists_natListHasGreaterCoordinate_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    hChain hBoundLength hLength

theorem exists_basisGreaterCoordinateWitness_singleton_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBoundLength : bound.length = W.net.places.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListBasisHasGreaterCoordinateWitness coords [bound] :=
  exists_basisGreaterCoordinateWitness_singleton_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    hChain hBoundLength hLength

end Petri
end Pm4Lean
