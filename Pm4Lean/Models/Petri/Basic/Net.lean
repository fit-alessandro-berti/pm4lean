import Pm4Lean.Models.Petri.Basic.Marking

namespace Pm4Lean
namespace Petri

/-- Arc weights from transitions to places for a Petri net. -/
abbrev ArcWeight (Transition Place : Type u) := Transition → Marking Place

/--
A basic place/transition Petri net.  The finite and decidable assumptions are
stored as explicit enumerating lists so algorithms and finite graph
constructions can be added without changing the semantic definitions.
-/
structure Net where
  Place : Type u
  Transition : Type v
  placeDecEq : DecidableEq Place
  transitionDecEq : DecidableEq Transition
  places : List Place
  transitions : List Transition
  places_complete : ∀ p : Place, p ∈ places
  transitions_complete : ∀ t : Transition, t ∈ transitions
  pre : Transition → Marking Place
  post : Transition → Marking Place

attribute [instance] Net.placeDecEq
attribute [instance] Net.transitionDecEq

namespace Net

variable (N : Net)

abbrev Marking := Petri.Marking N.Place

end Net
end Petri
end Pm4Lean
