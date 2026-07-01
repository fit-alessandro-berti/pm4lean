import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Large

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesHaveComparableCutPredecessor_of_bad_bound
    {W : WFNet} {n : Nat}
    (hBadBound :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n) :
    LargeCoveredPrefixCutSamplesHaveComparableCutPredecessor W n := by
  intro ts Mend hSeq samples hCovered
  exact FiringSequence.largeSamplesHaveComparablePrefixCutPredecessor_of_bad_bound
    (hBadBound ts Mend hSeq samples hCovered)

theorem hasLargeCoveredPrefixCutPredecessorThreshold_of_bad_bound
    {W : WFNet}
    (hBadBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    HasLargeCoveredPrefixCutPredecessorThreshold W := by
  obtain ⟨n, hAtN⟩ := hBadBound
  exact ⟨n,
    largeCoveredPrefixCutSamplesHaveComparableCutPredecessor_of_bad_bound
      hAtN⟩

end Petri
end Pm4Lean
