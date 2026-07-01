import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Definitions

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_of_subset
    {W : WFNet} {markings markings' : List W.Marking}
    (hSubset : ∀ M : W.Marking, M ∈ markings → M ∈ markings')
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
        W markings) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
      W markings' := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorMarkingsDominatedBy_of_subset
      hSubset
      (hCovered ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_subset
    {W : WFNet} {markings markings' : List W.Marking}
    (hSubset : ∀ M : W.Marking, M ∈ markings → M ∈ markings')
    (hCovered :
      LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
        W markings) :
    HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W :=
  ⟨markings',
    largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_of_subset
      hSubset hCovered⟩

end Petri
end Pm4Lean
