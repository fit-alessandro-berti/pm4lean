import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions.Covers.Sequence

namespace Pm4Lean
namespace Petri

/--
A self-cover observed at two cuts of one concrete firing sequence: `pref`
reaches `M`, and `pref ++ loop` reaches a strictly larger `M'`.
-/
def CutSelfCover (W : WFNet) : Prop :=
  ∃ pref loop : List W.net.Transition,
    ∃ M M' : W.Marking,
      FiringSequence W.net W.initial pref M ∧
        FiringSequence W.net W.initial (pref ++ loop) M' ∧
          M ≤ M' ∧ M ≠ M'

/--
A cut self-cover embedded in a longer concrete run.  This is the shape a
finite/Dickson extraction usually returns after factoring a long firing
sequence into prefix, loop, and suffix.
-/
def FactoredRunCutSelfCover (W : WFNet) : Prop :=
  ∃ pref loop suffix : List W.net.Transition,
    ∃ Mend M M' : W.Marking,
      FiringSequence W.net W.initial ((pref ++ loop) ++ suffix) Mend ∧
        FiringSequence W.net W.initial pref M ∧
          FiringSequence W.net W.initial (pref ++ loop) M' ∧
            M ≤ M' ∧ M ≠ M'

/--
A factored run self-cover stated with local prefix and loop executions.  The
cut at `pref ++ loop` can be reconstructed by appending those executions.
-/
def LocalFactoredRunCutSelfCover (W : WFNet) : Prop :=
  ∃ pref loop suffix : List W.net.Transition,
    ∃ Mend M M' : W.Marking,
      FiringSequence W.net W.initial ((pref ++ loop) ++ suffix) Mend ∧
        FiringSequence W.net W.initial pref M ∧
          FiringSequence W.net M loop M' ∧
            M ≤ M' ∧ M ≠ M'

end Petri
end Pm4Lean
