import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Cover.BadChain.Negative

namespace Pm4Lean
namespace Petri

theorem exists_noPredecessorLengthNormalizedBadCoverChain_of_basis_escape_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (n : Nat) :
    ∃ coordinates : List (List Nat),
      coordinates.length = n ∧
        LengthNormalizedBadCoverChain W coordinates :=
  exists_lengthNormalizedBadCoverChain_of_basis_escape_of_not_length_normalized_cover
    hNotCover n

theorem arbitrarilyLongNoPredecessorLengthNormalizedBadCoverChains_of_basis_escape_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ArbitrarilyLongLengthNormalizedBadCoverChains W :=
  arbitrarilyLongLengthNormalizedBadCoverChains_of_basis_escape_of_not_length_normalized_cover
    hNotCover

end Petri
end Pm4Lean
