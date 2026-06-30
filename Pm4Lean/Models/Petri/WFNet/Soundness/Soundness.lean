import Pm4Lean.Models.Petri.WFNet.Behavior.ProperCompletion
import Pm4Lean.Models.Petri.WFNet.Behavior.NoDeadTransitions
import Pm4Lean.Models.Petri.WFNet.Behavior.RelaxedSoundness

namespace Pm4Lean
namespace Petri

/-- Behavioral WF-net soundness decomposed into its standard predicates. -/
def BehaviorallySound (W : WFNet) : Prop :=
  OptionToComplete W ∧ ProperCompletion W ∧ NoDeadTransitions W

/--
The established name for behavioral soundness.  Structural WF-net validity is
kept separate in `ClassicalSoundness`.
-/
def Sound (W : WFNet) : Prop :=
  BehaviorallySound W

/-- Classical WF-net soundness combines structure and behavioral soundness. -/
def ClassicalSoundness (W : WFNet) : Prop :=
  WFNetStructure W ∧ Sound W

/-- Behavioral soundness without the no-dead-transition requirement. -/
def WeakSoundness (W : WFNet) : Prop :=
  OptionToComplete W ∧ ProperCompletion W

end Petri
end Pm4Lean
