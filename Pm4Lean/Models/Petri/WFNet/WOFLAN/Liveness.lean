import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit

namespace Pm4Lean
namespace Petri

/-- A transition is live when every reachable marking can reach one enabling it. -/
def LiveTransition (N : Net) (M₀ : N.Marking) (t : N.Transition) : Prop :=
  ∀ M : N.Marking, Reachable N M₀ M →
    ∃ M' : N.Marking, Reachable N M M' ∧ Enabled N M' t

/-- All transitions of a marked net are live. -/
def Live (N : Net) (M₀ : N.Marking) : Prop :=
  ∀ t : N.Transition, LiveTransition N M₀ t

end Petri
end Pm4Lean
