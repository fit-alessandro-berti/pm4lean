import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace

namespace Pm4Lean
namespace Petri

def LargeMarkingThresholdProducesComparablePrefixCutPairInRun
    (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        (∃ p : W.net.Place, n < Mend p) →
          FiringSequence.ComparablePrefixCutPairInRun
            W.net W.initial ts Mend

def HasLargeMarkingComparablePrefixCutPairInRunThreshold
    (W : WFNet) : Prop :=
  ∃ n : Nat,
    LargeMarkingThresholdProducesComparablePrefixCutPairInRun W n

theorem largeSequencesProduceComparableCutsInRun_of_largeMarkingThreshold
    {W : WFNet} {n : Nat}
    (hThreshold :
      LargeMarkingThresholdProducesComparablePrefixCutPairInRun W n) :
    LargeSequencesProduceComparableCutsInRun W := by
  intro hLarge
  obtain ⟨ts, Mend, hSeq, hLargeMarking⟩ := hLarge n
  exact comparableCutsInRun_of_comparableCutTrace
    (comparableCutTrace_of_inRun
      (FiringSequence.comparableCutTraceInRun_of_prefix
        (FiringSequence.prefixComparableCutTraceInRun_of_pair
          (hThreshold ts Mend hSeq hLargeMarking))))

theorem largeSequencesProduceComparableCutsInRun_of_largeMarkingThreshold_exists
    {W : WFNet}
    (hThreshold :
      HasLargeMarkingComparablePrefixCutPairInRunThreshold W) :
    LargeSequencesProduceComparableCutsInRun W := by
  obtain ⟨n, hAtN⟩ := hThreshold
  exact largeSequencesProduceComparableCutsInRun_of_largeMarkingThreshold hAtN

end Petri
end Pm4Lean
