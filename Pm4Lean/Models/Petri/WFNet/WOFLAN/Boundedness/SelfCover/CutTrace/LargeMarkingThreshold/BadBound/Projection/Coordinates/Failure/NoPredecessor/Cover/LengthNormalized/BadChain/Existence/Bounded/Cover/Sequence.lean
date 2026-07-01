import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Bounded.Cover.Basis

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_badCoverChainSequence_of_not_cover
    {W : WFNet}
    (hSequence :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W →
        ∃ f : Nat → List Nat, LengthNormalizedBadCoverChainSequence W f) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W := by
  classical
  exact Classical.byContradiction (fun hNotCover =>
    let hBadSequence := hSequence hNotCover
    match hBadSequence with
    | ⟨f, hSequence⟩ =>
        not_lengthNormalizedBadCoverChainSequence hSequence)

end Petri
end Pm4Lean
