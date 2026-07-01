import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Definitions.Covers.Reachable

namespace Pm4Lean
namespace Petri

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

end Petri
end Pm4Lean
