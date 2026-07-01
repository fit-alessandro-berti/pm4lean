import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Existence.Singleton

namespace Pm4Lean
namespace Petri

theorem exists_basis_escape_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat))
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords basis :=
  exists_basis_escape_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover basis hBasisLength

theorem exists_basis_greaterWitness_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat))
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis →
        upper.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo W.net.places.length (NatListMax basis.flatten)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          NatListBasisHasGreaterCoordinateWitness coords basis :=
  exists_basis_greaterWitness_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover basis hBasisLength

end Petri
end Pm4Lean
