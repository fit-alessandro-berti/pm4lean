import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Basic.Definition.Transition

namespace Pm4Lean
namespace Petri

/--
The short-circuited net used by WOFLAN: it preserves the original places and
transitions, and adds one transition consuming from the final place and
producing at the initial place.
-/
def shortCircuit (W : WFNet) : Net where
  Place := W.net.Place
  Transition := ShortCircuitTransition W
  placeDecEq := W.net.placeDecEq
  transitionDecEq := inferInstance
  places := W.net.places
  transitions :=
    W.net.transitions.map ShortCircuitTransition.original ++
      [ShortCircuitTransition.returnTransition]
  places_complete := W.net.places_complete
  transitions_complete := by
    intro t
    cases t with
    | inl t =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨t, W.net.transitions_complete t, rfl⟩
    | inr u =>
        cases u
        apply List.mem_append_right
        simp [ShortCircuitTransition.returnTransition]
  pre := fun t =>
    match t with
    | Sum.inl t => W.net.pre t
    | Sum.inr () => Marking.singleton W.o
  post := fun t =>
    match t with
    | Sum.inl t => W.net.post t
    | Sum.inr () => Marking.singleton W.i

namespace shortCircuit

variable (W : WFNet)

theorem places_eq :
    (shortCircuit W).places = W.net.places :=
  rfl

theorem pre_original (t : W.net.Transition) :
    (shortCircuit W).pre (ShortCircuitTransition.original t) = W.net.pre t :=
  rfl

theorem post_original (t : W.net.Transition) :
    (shortCircuit W).post (ShortCircuitTransition.original t) = W.net.post t :=
  rfl

theorem pre_return :
    (shortCircuit W).pre ShortCircuitTransition.returnTransition = W.final :=
  rfl

theorem post_return :
    (shortCircuit W).post ShortCircuitTransition.returnTransition = W.initial :=
  rfl

end shortCircuit

end Petri
end Pm4Lean
