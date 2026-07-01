import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.Samples.Predecessor

namespace Pm4Lean
namespace Petri

theorem largeMarkingThresholdProducesComparablePrefixCutPairInRun_of_samples
    {W : WFNet} {n : Nat}
    (hSamples : LargeCoveredPrefixCutSamplesContainComparablePair W n) :
    LargeMarkingThresholdProducesComparablePrefixCutPairInRun W n := by
  intro ts Mend hSeq hLarge
  obtain ⟨samples, hCovered⟩ :=
    FiringSequence.prefixCutSamples_cover_exists hSeq
  have hLargeSample :
      FiringSequence.ContainsLargePrefixCutSample samples n :=
    FiringSequence.containsLargePrefixCutSample_of_final
      hSeq hCovered hLarge
  exact FiringSequence.comparablePrefixCutPairInRun_of_sampleList
    (hSamples ts Mend hSeq samples hCovered hLargeSample)

theorem hasLargeMarkingComparablePrefixCutPairInRunThreshold_of_samples
    {W : WFNet}
    (hSamples : HasLargeCoveredPrefixCutSampleComparablePairThreshold W) :
    HasLargeMarkingComparablePrefixCutPairInRunThreshold W := by
  obtain ⟨n, hAtN⟩ := hSamples
  exact ⟨n,
    largeMarkingThresholdProducesComparablePrefixCutPairInRun_of_samples hAtN⟩

end Petri
end Pm4Lean
