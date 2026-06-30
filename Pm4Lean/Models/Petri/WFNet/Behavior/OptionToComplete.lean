import Pm4Lean.Models.Petri.WFNet.WFNetStructure
import Pm4Lean.Models.Petri.Semantics.Reachability

namespace Pm4Lean
namespace Petri

/-- Every reachable marking can still reach the final marking. -/
def OptionToComplete (W : WFNet) : Prop :=
  ∀ M : W.Marking, Reachable W.net W.initial M → Reachable W.net M W.final

end Petri
end Pm4Lean
