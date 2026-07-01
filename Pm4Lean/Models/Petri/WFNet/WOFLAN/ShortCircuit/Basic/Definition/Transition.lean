import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace Petri

/-- Transitions of the short-circuited WF-net. -/
abbrev ShortCircuitTransition (W : WFNet) :=
  Sum W.net.Transition Unit

namespace ShortCircuitTransition

variable {W : WFNet}

/-- An original transition embedded into the short-circuited net. -/
def original (t : W.net.Transition) : ShortCircuitTransition W :=
  Sum.inl t

/-- The fresh return transition from the final place to the initial place. -/
def returnTransition : ShortCircuitTransition W :=
  Sum.inr ()

end ShortCircuitTransition

end Petri
end Pm4Lean
