import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.ComparableCuts

namespace Pm4Lean
namespace Petri

theorem comparableCutsInRun_of_comparableCutTrace
    {W : WFNet}
    (hTrace : ComparableCutTrace W) :
    ComparableCutsInRun W :=
  factoredRunCutSelfCover_of_local hTrace

theorem comparableCutTrace_of_inRun
    {W : WFNet} {ts : List W.net.Transition} {Mend : W.Marking}
    (hTrace :
      FiringSequence.ComparableCutTraceInRun W.net W.initial ts Mend) :
    ComparableCutTrace W := by
  obtain ⟨pref, loop, suffix, M, M',
    hRun, hPref, hLoop, hLe, hNe⟩ :=
      FiringSequence.comparableCutTraceInRun_exists hTrace
  exact ⟨pref, loop, suffix, Mend, M, M',
    hRun,
    hPref,
    hLoop,
    hLe,
    hNe⟩

end Petri
end Pm4Lean
