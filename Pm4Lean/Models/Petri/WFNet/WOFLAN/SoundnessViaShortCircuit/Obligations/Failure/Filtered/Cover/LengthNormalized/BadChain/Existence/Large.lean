import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Finiteness

namespace Pm4Lean
namespace Petri

theorem exists_large_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        (NatListsUpTo W.net.places.length k).length <
          coordinates.length ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ∃ x : Nat, x ∈ coords ∧ k < x :=
  exists_large_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover k

end Petri
end Pm4Lean
