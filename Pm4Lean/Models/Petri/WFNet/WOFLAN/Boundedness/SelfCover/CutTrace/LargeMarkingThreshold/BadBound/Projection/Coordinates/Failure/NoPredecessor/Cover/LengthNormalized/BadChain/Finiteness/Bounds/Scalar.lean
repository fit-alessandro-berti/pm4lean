import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic
import Pm4Lean.Util.NatListBox.LowerCone

namespace Pm4Lean
namespace Petri

theorem length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_bounded
    {W : WFNet} {coordinates : List (List Nat)} {k : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        ∀ x : Nat, x ∈ coords → x ≤ k) :
    coordinates.length ≤
      (NatListsUpTo W.net.places.length k).length :=
  length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
    (not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain)
    (length_eq_of_mem_lengthNormalizedBadCoverChain hChain)
    hBound

theorem not_length_gt_natListsUpTo_length_of_lengthNormalizedBadCoverChain_bounded
    {W : WFNet} {coordinates : List (List Nat)} {k : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        ∀ x : Nat, x ∈ coords → x ≤ k) :
    ¬ (NatListsUpTo W.net.places.length k).length <
      coordinates.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_bounded
      hChain hBound)
    hLength

end Petri
end Pm4Lean
