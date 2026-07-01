import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Bounded.Cover

namespace Pm4Lean
namespace Petri

theorem not_exists_badCoverChains_basis_dominated_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ¬ ∃ basis : List (List Nat),
      ∀ coordinates : List (List Nat),
        LengthNormalizedBadCoverChain W coordinates →
          NatListBasisDominatesAll coordinates basis := by
  intro hDominated
  exact hNotCover
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_basis_dominated
      hDominated)

theorem exists_badCoverChain_not_dominatedBy_basis_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (basis : List (List Nat)) :
    ∃ coordinates : List (List Nat),
      LengthNormalizedBadCoverChain W coordinates ∧
        ∃ coords : List Nat, coords ∈ coordinates ∧
          ¬ NatListDominatedBy coords basis := by
  classical
  exact Classical.byContradiction (fun hNoEscape =>
    let hDominated :
        ∃ basis : List (List Nat),
          ∀ coordinates : List (List Nat),
            LengthNormalizedBadCoverChain W coordinates →
              NatListBasisDominatesAll coordinates basis := by
      refine ⟨basis, ?_⟩
      intro coordinates hChain coords hCoordsMem
      by_cases hDominated : NatListDominatedBy coords basis
      · exact hDominated
      · exact False.elim
          (hNoEscape ⟨coordinates, hChain, coords, hCoordsMem, hDominated⟩)
    not_exists_badCoverChains_basis_dominated_of_not_length_normalized_cover
      hNotCover hDominated)

end Petri
end Pm4Lean
