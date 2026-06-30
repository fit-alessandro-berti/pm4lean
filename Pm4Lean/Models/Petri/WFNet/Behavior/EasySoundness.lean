import Pm4Lean.Models.Petri.WFNet.Behavior.OptionToComplete

namespace Pm4Lean
namespace Petri

/-- The final marking is reachable from the initial marking. -/
def EasySoundness (W : WFNet) : Prop :=
  Reachable W.net W.initial W.final

theorem option_to_complete_implies_easy_soundness {W : WFNet}
    (h : OptionToComplete W) : EasySoundness W :=
  h W.initial (Reachable.refl W.initial)

end Petri
end Pm4Lean
