import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Definitions

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_cover
    {W : WFNet}
    (hCovered :
      HasLargeCoveredPrefixCutNoPredecessorMarkingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W := by
  obtain ⟨markings, hCoveredBy⟩ := hCovered
  refine ⟨markings, ?_⟩
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorMarkingsDominatedBy_of_covered
      (hCoveredBy ts Mend hSeq samples hSamplesCovered)

end Petri
end Pm4Lean
