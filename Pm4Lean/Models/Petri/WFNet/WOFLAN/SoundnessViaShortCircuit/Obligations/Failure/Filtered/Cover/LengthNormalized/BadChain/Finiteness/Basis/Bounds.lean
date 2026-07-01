import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Singleton

namespace Pm4Lean
namespace Petri

theorem length_le_natListsUpTo_length_of_noPredecessorLengthNormalizedBadCoverChain_basis_dominated
    {W : WFNet} {coordinates basis : List (List Nat)} {n : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll coordinates basis) :
    coordinates.length ≤
      (NatListsUpTo n (NatListMax basis.flatten)).length :=
  length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_basis_dominated
    hChain hBasisLength hDominates

theorem not_length_gt_natListsUpTo_length_of_noPredecessorLengthNormalizedBadCoverChain_basis_dominated
    {W : WFNet} {coordinates basis : List (List Nat)} {n : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll coordinates basis) :
    ¬ (NatListsUpTo n (NatListMax basis.flatten)).length <
      coordinates.length :=
  not_length_gt_natListsUpTo_length_of_lengthNormalizedBadCoverChain_basis_dominated
    hChain hBasisLength hDominates

end Petri
end Pm4Lean
