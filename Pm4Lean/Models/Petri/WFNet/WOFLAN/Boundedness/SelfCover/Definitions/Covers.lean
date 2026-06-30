import Pm4Lean.Models.Petri.Semantics.Monotonicity
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Original

namespace Pm4Lean
namespace Petri

/--
A reachable self-covering pair: from a reachable marking `M`, the original net
can reach a strictly larger marking `M'`.
-/
def ReachableSelfCover (W : WFNet) : Prop :=
  ∃ M M' : W.Marking,
    Reachable W.net W.initial M ∧
      Reachable W.net M M' ∧
        M ≤ M' ∧ M ≠ M'

/--
A concrete firing-sequence self-cover: after a prefix from the initial marking,
some continuation reaches a strictly larger marking.
-/
def FiringSequenceSelfCover (W : WFNet) : Prop :=
  ∃ pref loop : List W.net.Transition,
    ∃ M M' : W.Marking,
      FiringSequence W.net W.initial pref M ∧
        FiringSequence W.net M loop M' ∧
          M ≤ M' ∧ M ≠ M'

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

/--
A concrete run with two comparable cuts.  This names the factored-run cut
self-cover shape as the direct target expected from a finite/Dickson
extraction over cuts of one long sequence.
-/
abbrev ComparableCutsInRun (W : WFNet) : Prop :=
  FactoredRunCutSelfCover W

end Petri
end Pm4Lean
