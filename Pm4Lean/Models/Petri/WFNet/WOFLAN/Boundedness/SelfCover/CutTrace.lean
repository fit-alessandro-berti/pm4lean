import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.ComparableCuts
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.LongRuns

namespace Pm4Lean
namespace Petri

theorem comparableCutsInRun_of_comparableCutTrace
    {W : WFNet}
    (hTrace : ComparableCutTrace W) :
    ComparableCutsInRun W :=
  factoredRunCutSelfCover_of_local hTrace

theorem longRunsProduceComparableCutsInRun_of_cutTrace
    {W : WFNet}
    (hExtract : LongRunsProduceComparableCutTrace W) :
    LongRunsProduceComparableCutsInRun W := by
  intro hLong
  exact comparableCutsInRun_of_comparableCutTrace (hExtract hLong)

/--
A finite threshold for the final extraction: every concrete run longer than
`n` contains a comparable cut trace.  This is the expected output shape of a
finite/Dickson argument over the cuts of one run.
-/
def LongRunThresholdProducesComparableCutTrace (W : WFNet) (n : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        n < ts.length →
          ComparableCutTrace W

def HasLongRunComparableCutTraceThreshold (W : WFNet) : Prop :=
  ∃ n : Nat, LongRunThresholdProducesComparableCutTrace W n

theorem longRunsProduceComparableCutTrace_of_threshold
    {W : WFNet} {n : Nat}
    (hThreshold : LongRunThresholdProducesComparableCutTrace W n) :
    LongRunsProduceComparableCutTrace W := by
  intro hLong
  obtain ⟨ts, Mend, hSeq, hLen⟩ := hLong n
  exact hThreshold ts Mend hSeq hLen

theorem longRunsProduceComparableCutTrace_of_threshold_exists
    {W : WFNet}
    (hThreshold : HasLongRunComparableCutTraceThreshold W) :
    LongRunsProduceComparableCutTrace W := by
  obtain ⟨n, hAtN⟩ := hThreshold
  exact longRunsProduceComparableCutTrace_of_threshold hAtN

theorem longRunsProduceComparableCutsInRun_of_threshold
    {W : WFNet} {n : Nat}
    (hThreshold : LongRunThresholdProducesComparableCutTrace W n) :
    LongRunsProduceComparableCutsInRun W :=
  longRunsProduceComparableCutsInRun_of_cutTrace
    (longRunsProduceComparableCutTrace_of_threshold hThreshold)

theorem longRunsProduceComparableCutsInRun_of_threshold_exists
    {W : WFNet}
    (hThreshold : HasLongRunComparableCutTraceThreshold W) :
    LongRunsProduceComparableCutsInRun W :=
  longRunsProduceComparableCutsInRun_of_cutTrace
    (longRunsProduceComparableCutTrace_of_threshold_exists hThreshold)

end Petri
end Pm4Lean
