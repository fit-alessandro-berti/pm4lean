import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Cover.BadChain.Positive
import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain.Existence.Large

namespace Pm4Lean
namespace Petri

theorem not_exists_noPredecessorLengthNormalizedBadCoverChains_bounded_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ¬ ∃ k : Nat,
      ∀ coordinates : List (List Nat),
        LengthNormalizedBadCoverChain W coordinates →
          ∀ coords : List Nat, coords ∈ coordinates →
            ∀ x : Nat, x ∈ coords → x ≤ k := by
  intro hBounded
  exact hNotCover
    (noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_bounded
      hBounded)

theorem exists_noPredecessorLengthNormalizedBadCoverChain_escaping_bound_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (k : Nat) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ∃ x : Nat, x ∈ coords ∧ k < x := by
  obtain ⟨coordinates, hChain, _hLength, coords, hCoordsMem,
    x, hXMem, hLarge⟩ :=
    exists_large_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
      hNotCover k
  exact ⟨coordinates, hChain, coords, hCoordsMem, x, hXMem, hLarge⟩

theorem not_exists_noPredecessorLengthNormalizedBadCoverChain_basis_dominated_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ¬ ∃ basis : List (List Nat),
      ∀ coordinates : List (List Nat),
        LengthNormalizedBadCoverChain W coordinates →
          NatListBasisDominatesAll coordinates basis :=
  not_exists_badCoverChains_basis_dominated_of_not_length_normalized_cover
    hNotCover

theorem exists_noPredecessorLengthNormalizedBadCoverChain_not_dominatedBy_basis_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat)) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords basis :=
  exists_badCoverChain_not_dominatedBy_basis_of_not_length_normalized_cover
    hNotCover basis

end Petri
end Pm4Lean
