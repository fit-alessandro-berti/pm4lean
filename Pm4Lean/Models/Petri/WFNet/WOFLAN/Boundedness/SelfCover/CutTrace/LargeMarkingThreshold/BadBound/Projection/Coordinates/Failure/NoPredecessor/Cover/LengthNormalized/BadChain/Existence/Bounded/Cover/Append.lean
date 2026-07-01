import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Bounded.Cover.Sequence

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_appendExtension_of_not_cover
    {W : WFNet}
    (hExtend :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W →
        LengthNormalizedBadCoverChainAppendExtension W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W := by
  classical
  exact Classical.byContradiction (fun hNotCover =>
    not_lengthNormalizedBadCoverChainAppendExtension
      (hExtend hNotCover))

end Petri
end Pm4Lean
