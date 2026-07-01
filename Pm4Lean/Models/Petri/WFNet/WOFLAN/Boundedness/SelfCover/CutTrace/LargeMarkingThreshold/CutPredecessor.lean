import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.Samples

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesHaveComparableCutPredecessor
    (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.LargeSamplesHaveComparablePrefixCutPredecessor
              samples n

def HasLargeCoveredPrefixCutPredecessorThreshold
    (W : WFNet) : Prop :=
  ∃ n : Nat, LargeCoveredPrefixCutSamplesHaveComparableCutPredecessor W n

theorem largeCoveredPrefixCutSamplesHaveComparablePredecessor_of_cut
    {W : WFNet} {n : Nat}
    (hCutPredecessor :
      LargeCoveredPrefixCutSamplesHaveComparableCutPredecessor W n) :
    LargeCoveredPrefixCutSamplesHaveComparablePredecessor W n := by
  intro ts Mend hSeq samples hCovered
  exact FiringSequence.largeSamplesHaveComparablePrefixPredecessor_of_cut
    hCovered (hCutPredecessor ts Mend hSeq samples hCovered)

theorem hasLargeCoveredPrefixCutSamplePredecessorThreshold_of_cut
    {W : WFNet}
    (hCutPredecessor : HasLargeCoveredPrefixCutPredecessorThreshold W) :
    HasLargeCoveredPrefixCutSamplePredecessorThreshold W := by
  obtain ⟨n, hAtN⟩ := hCutPredecessor
  exact ⟨n,
    largeCoveredPrefixCutSamplesHaveComparablePredecessor_of_cut hAtN⟩

end Petri
end Pm4Lean
