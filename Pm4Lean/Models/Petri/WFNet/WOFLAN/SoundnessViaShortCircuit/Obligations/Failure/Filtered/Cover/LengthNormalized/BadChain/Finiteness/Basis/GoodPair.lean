import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness.Basis.Escape

namespace Pm4Lean
namespace Petri

theorem containsNatListLePair_of_noPredecessorLengthNormalizedBadCoverChain_length_gt_basis_dominated
    {coordinates basis : List (List Nat)} {n : Nat}
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll coordinates basis)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length <
        coordinates.length) :
    ContainsNatListLePair coordinates :=
  containsNatListLePair_of_lengthNormalizedBadCoverChain_length_gt_basis_dominated
    hBasisLength hDominates hLength

end Petri
end Pm4Lean
