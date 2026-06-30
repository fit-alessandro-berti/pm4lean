import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness

namespace Pm4Lean
namespace Petri

/-- A marked net is bounded by a global token bound. -/
def BoundedBy (N : Net) (M₀ : N.Marking) (k : Nat) : Prop :=
  ∀ M : N.Marking, Reachable N M₀ M → ∀ p : N.Place, M p ≤ k

/-- A marked net has some finite global token bound. -/
def Bounded (N : Net) (M₀ : N.Marking) : Prop :=
  ∃ k : Nat, BoundedBy N M₀ k

/-- A marked net is safe when each place always has at most one token. -/
def Safe (N : Net) (M₀ : N.Marking) : Prop :=
  BoundedBy N M₀ 1

end Petri
end Pm4Lean
