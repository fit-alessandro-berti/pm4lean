import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.BadChain

namespace Pm4Lean
namespace Petri

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_bounded
    {W : WFNet}
    (hBounded :
      ∃ k : Nat,
        ∀ coordinates : List (List Nat),
          LengthNormalizedBadCoverChain W coordinates →
            ∀ coords : List Nat, coords ∈ coordinates →
              ∀ x : Nat, x ∈ coords → x ≤ k) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_bounded
    hBounded

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_basis_dominated
    {W : WFNet}
    (hDominated :
      ∃ basis : List (List Nat),
        ∀ coordinates : List (List Nat),
          LengthNormalizedBadCoverChain W coordinates →
            NatListBasisDominatesAll coordinates basis) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChains_basis_dominated
    hDominated

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChainSequence_of_not_cover
    {W : WFNet}
    (hSequence :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W →
        ∃ f : Nat → List Nat, LengthNormalizedBadCoverChainSequence W f) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChainSequence_of_not_cover
    hSequence

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_appendExtension_of_not_cover
    {W : WFNet}
    (hExtend :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W →
        LengthNormalizedBadCoverChainAppendExtension W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_appendExtension_of_not_cover
    hExtend

end Petri
end Pm4Lean
