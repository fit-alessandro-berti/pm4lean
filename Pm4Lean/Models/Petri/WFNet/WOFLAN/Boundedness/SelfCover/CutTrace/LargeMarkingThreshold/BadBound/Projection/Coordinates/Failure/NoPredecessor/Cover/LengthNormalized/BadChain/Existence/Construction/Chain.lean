import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Construction.Prepend

namespace Pm4Lean
namespace Petri

theorem exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (n : Nat) :
    ∃ coordinates : List (List Nat),
      coordinates.length = n ∧
        LengthNormalizedBadCoverChain W coordinates := by
  have hPrepend :
      LengthNormalizedBadCoverChainPrependExtension W :=
    lengthNormalizedBadCoverChainPrependExtension_of_not_length_normalized_cover
      hNotCover
  induction n with
  | zero =>
      exact ⟨[], rfl, trivial⟩
  | succ n ih =>
      obtain ⟨coordinates, hCoordinatesLengthEq, hChain⟩ := ih
      obtain ⟨coords, hConsChain⟩ := hPrepend coordinates hChain
      exact ⟨coords :: coordinates, by simp [hCoordinatesLengthEq],
        hConsChain⟩

theorem arbitrarilyLongLengthNormalizedBadCoverChains_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ArbitrarilyLongLengthNormalizedBadCoverChains W := by
  intro n
  exact exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover n

end Petri
end Pm4Lean
