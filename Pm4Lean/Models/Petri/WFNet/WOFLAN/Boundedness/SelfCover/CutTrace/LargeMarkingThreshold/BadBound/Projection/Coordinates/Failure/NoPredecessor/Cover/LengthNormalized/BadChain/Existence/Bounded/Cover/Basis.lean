import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Bounded.Cover.Bounded

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_basis_dominated
    {W : WFNet}
    (hDominated :
      ∃ basis : List (List Nat),
        ∀ coordinates : List (List Nat),
          LengthNormalizedBadCoverChain W coordinates →
            NatListBasisDominatesAll coordinates basis) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W := by
  obtain ⟨basis, hDominated⟩ := hDominated
  apply hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_bounded
  exact ⟨NatListMax basis.flatten, by
    intro coordinates hChain coords hCoordsMem x hXMem
    exact forall_le_natListMax_flatten_of_natListDominatedBy
      (hDominated coordinates hChain coords hCoordsMem)
      x hXMem⟩

end Petri
end Pm4Lean
