import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Escape
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_bounded
    {W : WFNet}
    (hBounded :
      ∃ k : Nat,
        ∀ coordinates : List (List Nat),
          LengthNormalizedBadCoverChain W coordinates →
            ∀ coords : List Nat, coords ∈ coordinates →
              ∀ x : Nat, x ∈ coords → x ≤ k) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W := by
  classical
  obtain ⟨k, hBounded⟩ := hBounded
  exact Classical.byContradiction (fun hNotCover =>
    let hLargeChain :=
      exists_large_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
        hNotCover k
    match hLargeChain with
    | ⟨coordinates, hChain, _hLength, coords, hCoordsMem,
        x, hXMem, hLarge⟩ =>
        Nat.not_lt_of_ge
          (hBounded coordinates hChain coords hCoordsMem x hXMem)
          hLarge)

end Petri
end Pm4Lean
