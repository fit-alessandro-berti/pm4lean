import Pm4Lean.Models.Petri.Behavior.Boundedness.Samples.ExplicitBound
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Bridge

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
    {W : WFNet}
    (hCovered :
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W := by
  obtain ⟨markings, hCoveredBy⟩ := hCovered
  refine ⟨NatListMax (sampleMarkingTokenSums W.net markings), ?_⟩
  intro ts Mend hSeq samples hSamplesCovered
  exact FiringSequence.noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    (hCoveredBy ts Mend hSeq samples hSamplesCovered)
    (fun M hMem =>
      sampleMarking_le_natListMax_tokenSums (N := W.net) hMem)

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsCovered
    {W : WFNet}
    (hCovered :
      HasLargeCoveredPrefixCutNoPredecessorMarkingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
    (hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_cover
      hCovered)

end Petri
end Pm4Lean
