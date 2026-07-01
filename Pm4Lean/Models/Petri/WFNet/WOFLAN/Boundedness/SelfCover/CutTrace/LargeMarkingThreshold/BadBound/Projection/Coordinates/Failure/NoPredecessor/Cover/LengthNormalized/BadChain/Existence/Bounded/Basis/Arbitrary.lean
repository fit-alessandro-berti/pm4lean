import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Bounded.Basis.Negative

namespace Pm4Lean
namespace Petri

theorem exists_lengthNormalizedBadCoverChain_of_basis_escape_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (n : Nat) :
    ∃ coordinates : List (List Nat),
      coordinates.length = n ∧
        LengthNormalizedBadCoverChain W coordinates := by
  obtain ⟨coordinates, hLength, hCoordLength, hNoPair⟩ :=
    exists_not_containsNatListLePair_list_of_forall_basis_escape
      (P := fun coords : List Nat => coords.length = W.net.places.length)
      (fun basis => by
        obtain ⟨chainCoordinates, hChain, coords, hCoordsMem,
          hNotDominated⟩ :=
          exists_badCoverChain_not_dominatedBy_basis_of_not_length_normalized_cover
            hNotCover basis
        exact ⟨coords,
          length_eq_of_mem_lengthNormalizedBadCoverChain
            hChain coords hCoordsMem,
          hNotDominated⟩)
      n
  exact ⟨coordinates, hLength,
    lengthNormalizedBadCoverChain_of_not_containsNatListLePair
      hCoordLength hNoPair⟩

theorem arbitrarilyLongLengthNormalizedBadCoverChains_of_basis_escape_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ArbitrarilyLongLengthNormalizedBadCoverChains W := by
  intro n
  exact exists_lengthNormalizedBadCoverChain_of_basis_escape_of_not_length_normalized_cover
    hNotCover n

end Petri
end Pm4Lean
