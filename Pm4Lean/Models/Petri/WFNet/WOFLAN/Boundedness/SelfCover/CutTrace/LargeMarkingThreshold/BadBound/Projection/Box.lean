import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Definitions

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_boundedBox
    {W : WFNet} {k : Nat}
    (hBounded : LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W k) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
      W (Marking.boundedPlaceValueMarkings W.net k) := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorMarkingsDominatedBy_boundedBox
      (hBounded ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_bound
    {W : WFNet} (hBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W := by
  obtain ⟨k, hBounded⟩ := hBound
  exact ⟨Marking.boundedPlaceValueMarkings W.net k,
    largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_boundedBox
      hBounded⟩

end Petri
end Pm4Lean
