import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Bounded

namespace Pm4Lean
namespace Petri

theorem length_le_natListsUpTo_length_of_noPredecessorLengthNormalizedBadCoverChain_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    coordinates.length ≤
      (NatListsUpTo bound.length (NatListMax bound)).length :=
  length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_natListLe_bound
    hChain hBound

theorem not_length_gt_natListsUpTo_length_of_noPredecessorLengthNormalizedBadCoverChain_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    ¬ (NatListsUpTo bound.length (NatListMax bound)).length <
      coordinates.length :=
  not_length_gt_natListsUpTo_length_of_lengthNormalizedBadCoverChain_natListLe_bound
    hChain hBound

end Petri
end Pm4Lean
