import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Singleton.Bounds

namespace Pm4Lean
namespace Petri

theorem containsNatListLePair_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_natListLe_bound
    {coordinates : List (List Nat)} {bound : List Nat}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length <
        coordinates.length)
    (hBound :
      ∀ coords : List Nat, coords ∈ coordinates →
        NatListLe coords bound) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_natListLe_bound
    hLength hBound

end Petri
end Pm4Lean
