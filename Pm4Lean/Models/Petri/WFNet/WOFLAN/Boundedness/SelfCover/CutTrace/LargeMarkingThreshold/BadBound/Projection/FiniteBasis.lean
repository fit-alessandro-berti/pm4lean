import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Bound
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.FiniteBasis

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome_of_markingsDominated
    {W : WFNet} {markings : List W.Marking}
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
        W markings) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome
      W [NatListMax (sampleMarkingTokenSums W.net markings)] := by
  intro ts Mend hSeq samples hSamplesCovered
  refine ⟨NatListMax (sampleMarkingTokenSums W.net markings), by simp, ?_⟩
  exact FiringSequence.noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    (hCovered ts Mend hSeq samples hSamplesCovered)
    (fun M hMem =>
      sampleMarking_le_natListMax_tokenSums (N := W.net) hMem)

theorem hasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis_of_markingsDominated
    {W : WFNet}
    (hCovered :
      HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis W := by
  obtain ⟨markings, hCoveredBy⟩ := hCovered
  exact ⟨[NatListMax (sampleMarkingTokenSums W.net markings)],
    largeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome_of_markingsDominated
      hCoveredBy⟩

end Petri
end Pm4Lean
