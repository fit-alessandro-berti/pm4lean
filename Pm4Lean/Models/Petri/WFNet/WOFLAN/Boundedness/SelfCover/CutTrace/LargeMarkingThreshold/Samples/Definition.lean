import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesContainComparablePair
    (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.ContainsLargePrefixCutSample samples n →
              FiringSequence.ContainsComparablePrefixCutSamplePair samples

def HasLargeCoveredPrefixCutSampleComparablePairThreshold
    (W : WFNet) : Prop :=
  ∃ n : Nat, LargeCoveredPrefixCutSamplesContainComparablePair W n

def LargeCoveredPrefixCutSamplesHaveComparablePredecessor
    (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.LargeSamplesHaveComparablePrefixPredecessor
              samples n

def HasLargeCoveredPrefixCutSamplePredecessorThreshold
    (W : WFNet) : Prop :=
  ∃ n : Nat, LargeCoveredPrefixCutSamplesHaveComparablePredecessor W n

end Petri
end Pm4Lean
