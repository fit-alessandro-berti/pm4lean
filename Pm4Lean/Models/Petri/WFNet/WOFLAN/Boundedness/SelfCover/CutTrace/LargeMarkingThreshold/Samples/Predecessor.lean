import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.Samples.Definition

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesContainComparablePair_of_predecessor
    {W : WFNet} {n : Nat}
    (hPredecessor :
      LargeCoveredPrefixCutSamplesHaveComparablePredecessor W n) :
    LargeCoveredPrefixCutSamplesContainComparablePair W n := by
  intro ts Mend hSeq samples hCovered hLarge
  exact FiringSequence.containsComparablePrefixCutSamplePair_of_large_predecessor
    hLarge (hPredecessor ts Mend hSeq samples hCovered)

theorem hasLargeCoveredPrefixCutSampleComparablePairThreshold_of_predecessor
    {W : WFNet}
    (hPredecessor :
      HasLargeCoveredPrefixCutSamplePredecessorThreshold W) :
    HasLargeCoveredPrefixCutSampleComparablePairThreshold W := by
  obtain ⟨n, hAtN⟩ := hPredecessor
  exact ⟨n,
    largeCoveredPrefixCutSamplesContainComparablePair_of_predecessor hAtN⟩

end Petri
end Pm4Lean
