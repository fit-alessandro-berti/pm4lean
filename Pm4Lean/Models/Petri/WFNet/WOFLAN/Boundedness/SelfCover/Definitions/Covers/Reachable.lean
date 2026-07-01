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

end Petri
end Pm4Lean
