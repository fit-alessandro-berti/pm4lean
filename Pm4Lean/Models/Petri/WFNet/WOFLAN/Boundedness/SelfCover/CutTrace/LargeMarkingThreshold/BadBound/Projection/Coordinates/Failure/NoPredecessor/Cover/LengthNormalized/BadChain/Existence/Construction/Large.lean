import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Construction.Chain
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness

namespace Pm4Lean
namespace Petri

theorem exists_large_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
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
          ∃ x : Nat, x ∈ coords ∧ k < x := by
  obtain ⟨coordinates, hLengthEq, hChain⟩ :=
    exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
      hNotCover
      ((NatListsUpTo W.net.places.length k).length + 1)
  have hLength :
      (NatListsUpTo W.net.places.length k).length <
        coordinates.length := by
    simp [hLengthEq]
  exact ⟨coordinates, hChain, hLength,
    exists_large_coordinate_of_lengthNormalizedBadCoverChain_length_gt
      hChain hLength⟩

end Petri
end Pm4Lean
