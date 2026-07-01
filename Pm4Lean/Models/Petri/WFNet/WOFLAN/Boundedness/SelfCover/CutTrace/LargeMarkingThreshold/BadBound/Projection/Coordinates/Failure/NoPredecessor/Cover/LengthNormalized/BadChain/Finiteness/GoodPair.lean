import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness.Escape

namespace Pm4Lean
namespace Petri

theorem containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_basis_dominated
    {coordinates basis : List (List Nat)} {n : Nat}
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll coordinates basis)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length <
        coordinates.length) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_length_gt_natListsUpTo_length_of_basis_dominated
    hBasisLength hDominates hLength

theorem containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_bounded
    {W : WFNet} {coordinates : List (List Nat)} {k : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo W.net.places.length k).length <
        coordinates.length)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        ∀ x : Nat, x ∈ coords → x ≤ k) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_length_gt_natListsUpTo_length_of_forall
    hLength
    (length_eq_of_mem_lengthNormalizedBadCoverChain hChain)
    hBound

theorem containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {coordinates : List (List Nat)} {bound : List Nat}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_length_gt_natListsUpTo_length_of_natListLe_bound
    hLength hBound

end Petri
end Pm4Lean
