import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Existence.Large

namespace Pm4Lean
namespace Petri

theorem exists_singleton_bound_escape_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (bound : List Nat) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo bound.length (NatListMax bound)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords [bound] :=
  exists_singleton_bound_escape_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover bound

theorem exists_singleton_bound_greaterWitness_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    {bound : List Nat}
    (hBoundLength : bound.length = W.net.places.length) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo bound.length (NatListMax bound)).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          NatListBasisHasGreaterCoordinateWitness coords [bound] :=
  exists_singleton_bound_greaterWitness_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover hBoundLength

end Petri
end Pm4Lean
