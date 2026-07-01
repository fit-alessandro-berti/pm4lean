import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Prefix.Cycle
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions

namespace Pm4Lean
namespace Petri

/--
A non-strict cycle observed at equal cut markings inside one concrete run.
This records a removable/repeatable loop, not a strict self-cover.
-/
def EqualCutCycle (W : WFNet) : Prop :=
  ∃ pref loop suffix : List W.net.Transition,
    ∃ Mend M : W.Marking,
      FiringSequence W.net W.initial ((pref ++ loop) ++ suffix) Mend ∧
        FiringSequence W.net W.initial pref M ∧
          FiringSequence W.net M loop M

theorem equalCutCycle_of_equalPrefixCutCycleInRun
    {W : WFNet} {ts : List W.net.Transition} {Mend : W.Marking}
    (hCycle :
      FiringSequence.EqualPrefixCutCycleInRun
        W.net W.initial ts Mend) :
    EqualCutCycle W := by
  obtain ⟨pref, loop, suffix, M, hTs, hRun, hPref, hLoop⟩ := hCycle
  exact ⟨pref, loop, suffix, Mend, M,
    by simpa [hTs] using hRun,
    hPref,
    hLoop⟩

end Petri
end Pm4Lean
