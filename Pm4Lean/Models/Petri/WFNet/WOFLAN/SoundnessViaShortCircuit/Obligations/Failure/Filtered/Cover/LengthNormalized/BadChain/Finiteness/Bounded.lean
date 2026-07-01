import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Basic

namespace Pm4Lean
namespace Petri

theorem containsNatListLePair_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_bounded
    {W : WFNet} {coordinates : List (List Nat)} {k : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo W.net.places.length k).length <
        coordinates.length)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        ∀ x : Nat, x ∈ coords → x ≤ k) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_bounded
    hChain hLength hBound

end Petri
end Pm4Lean
