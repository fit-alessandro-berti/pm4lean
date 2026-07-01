import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Sequence
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Bound

namespace Pm4Lean
namespace Petri

theorem largeSequencesProduceComparableCutsInRun_of_noPredecessorBound
    {W : WFNet}
    (hBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    LargeSequencesProduceComparableCutsInRun W :=
  largeSequencesProduceComparableCutsInRun_of_largeMarkingThreshold_exists
    (hasLargeMarkingComparablePrefixCutPairInRunThreshold_of_samples
      (hasLargeCoveredPrefixCutSampleComparablePairThreshold_of_predecessor
        (hasLargeCoveredPrefixCutSamplePredecessorThreshold_of_cut
          (hasLargeCoveredPrefixCutPredecessorThreshold_of_bad_bound
            hBound))))

theorem largeSequencesProduceFiringSequenceSelfCover_of_noPredecessorBound
    {W : WFNet}
    (hBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    LargeSequencesProduceFiringSequenceSelfCover W :=
  largeSequencesProduceFiringSequenceSelfCover_of_cut
    (largeSequencesProduceCutSelfCover_of_factoredRun
      (largeSequencesProduceFactoredRunCutSelfCover_of_comparableCuts
        (largeSequencesProduceComparableCutsInRun_of_noPredecessorBound
          hBound)))

theorem largeSequencesProduceFiringSequenceSelfCover_of_noPredecessorMarkingDominatingCover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W) :
    LargeSequencesProduceFiringSequenceSelfCover W :=
  largeSequencesProduceFiringSequenceSelfCover_of_noPredecessorBound
    (hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
      hCover)

end Petri
end Pm4Lean
