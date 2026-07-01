import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness.Bounds.Scalar

namespace Pm4Lean
namespace Petri

theorem length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    coordinates.length ≤
      (NatListsUpTo bound.length (NatListMax bound)).length :=
  length_le_natListsUpTo_length_of_not_containsNatListLePair_of_natListLe_bound
    (not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain)
    hBound

theorem not_length_gt_natListsUpTo_length_of_lengthNormalizedBadCoverChain_natListLe_bound
    {W : WFNet} {coordinates : List (List Nat)} {bound : List Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    ¬ (NatListsUpTo bound.length (NatListMax bound)).length <
      coordinates.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_natListLe_bound
      hChain hBound)
    hLength

end Petri
end Pm4Lean
