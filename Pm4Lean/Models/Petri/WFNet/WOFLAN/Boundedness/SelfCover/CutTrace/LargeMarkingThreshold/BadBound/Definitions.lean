import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.CutPredecessor

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesWithoutPredecessorBounded
    (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.NoComparablePrefixCutPredecessorsBounded
              samples n

def HasLargeCoveredPrefixCutNoPredecessorBound
    (W : WFNet) : Prop :=
  ∃ n : Nat,
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n

def LargeCoveredPrefixCutNoPredecessorSampleAbove
    (W : WFNet) (k : Nat) : Prop :=
  ∃ ts : List W.net.Transition,
    ∃ Mend : W.Marking,
      ∃ _hSeq : FiringSequence W.net W.initial ts Mend,
        ∃ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples ∧
            ∃ sample :
              FiringSequence.PrefixCutSample W.net W.initial ts Mend,
              sample ∈ samples ∧
                ¬ FiringSequence.HasComparablePrefixCutPredecessor
                  sample ∧
                ∃ p : W.net.Place, k < sample.marking p

def ArbitrarilyLargeCoveredPrefixCutNoPredecessorSample
    (W : WFNet) : Prop :=
  ∀ k : Nat, LargeCoveredPrefixCutNoPredecessorSampleAbove W k

end Petri
end Pm4Lean
