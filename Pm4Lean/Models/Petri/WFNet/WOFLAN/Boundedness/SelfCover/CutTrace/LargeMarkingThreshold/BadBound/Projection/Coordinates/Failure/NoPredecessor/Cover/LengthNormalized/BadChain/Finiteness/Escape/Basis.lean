import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness.Escape.LowerCone

namespace Pm4Lean
namespace Petri

theorem exists_not_natListDominatedBy_of_lengthNormalizedBadCoverChain_length_gt_basis
    {W : WFNet} {coordinates basis : List (List Nat)} {n : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      ¬ NatListDominatedBy coords basis :=
  exists_not_natListDominatedBy_of_not_containsNatListLePair_length_gt_basis
    (not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain)
    hBasisLength hLength

theorem exists_basisGreaterCoordinateWitness_of_lengthNormalizedBadCoverChain_length_gt_basis
    {W : WFNet} {coordinates basis : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length)
    (hLength :
      (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      NatListBasisHasGreaterCoordinateWitness coords basis := by
  apply exists_basisGreaterCoordinateWitness_of_not_containsNatListLePair_length_gt_basis
  · exact not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain
  · exact length_eq_of_mem_lengthNormalizedBadCoverChain hChain
  · exact hBasisLength
  · exact hLength

end Petri
end Pm4Lean
