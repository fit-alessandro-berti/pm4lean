import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Basis.Bounds

namespace Pm4Lean
namespace Petri

theorem exists_not_natListDominatedBy_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_basis
    {W : WFNet} {coordinates basis : List (List Nat)} {n : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      ¬ NatListDominatedBy coords basis :=
  exists_not_natListDominatedBy_of_lengthNormalizedBadCoverChain_length_gt_basis
    hChain hBasisLength hLength

theorem exists_basisGreaterCoordinateWitness_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_basis
    {W : WFNet} {coordinates basis : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length)
    (hLength :
      (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListBasisHasGreaterCoordinateWitness coords basis :=
  exists_basisGreaterCoordinateWitness_of_lengthNormalizedBadCoverChain_length_gt_basis
    hChain hBasisLength hLength

end Petri
end Pm4Lean
