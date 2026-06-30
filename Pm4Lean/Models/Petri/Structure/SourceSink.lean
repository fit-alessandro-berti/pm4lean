import Pm4Lean.Models.Petri.Structure.Path

namespace Pm4Lean
namespace Petri

/-- A place with no incoming transition arcs. -/
def SourcePlace (N : Net) (p : N.Place) : Prop :=
  ∀ t : N.Transition, N.post t p = 0

/-- A place with no outgoing transition arcs. -/
def SinkPlace (N : Net) (p : N.Place) : Prop :=
  ∀ t : N.Transition, N.pre t p = 0

/-- Every graph node is on a path between two distinguished places. -/
def EveryNodeOnPath (N : Net) (i o : N.Place) : Prop :=
  ∀ x : Node N, Path N (.place i) x ∧ Path N x (.place o)

end Petri
end Pm4Lean
