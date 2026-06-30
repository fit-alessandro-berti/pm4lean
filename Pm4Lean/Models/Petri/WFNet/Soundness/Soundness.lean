import Pm4Lean.Models.Petri.WFNet.Behavior.ProperCompletion
import Pm4Lean.Models.Petri.WFNet.Behavior.NoDeadTransitions
import Pm4Lean.Models.Petri.WFNet.Behavior.RelaxedSoundness

namespace Pm4Lean
namespace Petri

/-- Classical WF-net soundness decomposed into its standard predicates. -/
def Sound (W : WFNet) : Prop :=
  OptionToComplete W ∧ ProperCompletion W ∧ NoDeadTransitions W

/-- Behavioral soundness without the no-dead-transition requirement. -/
def WeakSoundness (W : WFNet) : Prop :=
  OptionToComplete W ∧ ProperCompletion W

end Petri
end Pm4Lean
