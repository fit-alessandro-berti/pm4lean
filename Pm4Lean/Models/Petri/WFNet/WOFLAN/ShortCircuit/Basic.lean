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

theorem return_enabled_at_final :
    Enabled (shortCircuit W) W.final ShortCircuitTransition.returnTransition := by
  intro p
  exact Nat.le_refl (W.final p)

theorem return_enabled_iff_final_covered (M : W.Marking) :
    Enabled (shortCircuit W) M ShortCircuitTransition.returnTransition ↔
      W.final ≤ M :=
  Iff.rfl

theorem original_enabled_iff (M : W.Marking) (t : W.net.Transition) :
    Enabled (shortCircuit W) M (ShortCircuitTransition.original t) ↔
      Enabled W.net M t :=
  Iff.rfl

theorem fire_original (M : W.Marking) (t : W.net.Transition) :
    fire (shortCircuit W) M (ShortCircuitTransition.original t) =
      fire W.net M t :=
  rfl

theorem fire_return (M : W.Marking) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition =
      M - W.final + W.initial :=
  rfl

theorem fire_return_apply (M : W.Marking) (p : W.net.Place) :
    fire (shortCircuit W) M ShortCircuitTransition.returnTransition p =
      M p - W.final p + W.initial p :=
  rfl

theorem remainder_le_fire_return (M : W.Marking) (p : W.net.Place) :
    M p - W.final p ≤
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.le_add_right _ _

theorem fire_return_positive_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    0 < fire (shortCircuit W) M ShortCircuitTransition.returnTransition p :=
  Nat.lt_of_lt_of_le hPositive (remainder_le_fire_return W M p)

theorem initial_lt_fire_return_of_positive_remainder
    {M : W.Marking} {p : W.net.Place}
    (hPositive : 0 < M p - W.final p) :
    W.initial p <
      fire (shortCircuit W) M ShortCircuitTransition.returnTransition p := by
  rw [fire_return_apply]
  exact Nat.lt_add_of_pos_left hPositive

theorem reachable_fire_return_of_final_covered
    {M : W.Marking}
    (hFinalCovered : W.final ≤ M) :
    Reachable (shortCircuit W) M (M - W.final + W.initial) := by
  simpa [fire_return] using
    (Reachable.of_enabled
      ((return_enabled_iff_final_covered W M).2 hFinalCovered))

theorem step_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Step (shortCircuit W) M (fire W.net M t) :=
  Step.fire ((original_enabled_iff W M t).2 hEnabled)

theorem step_original_to_shortCircuit {M M' : W.Marking}
    (hStep : Step W.net M M') :
    Step (shortCircuit W) M M' := by
  cases hStep with
  | fire hEnabled =>
      simpa [fire_original] using step_original_of_enabled W hEnabled

theorem reachable_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Reachable (shortCircuit W) M (fire W.net M t) :=
  Reachable.of_step (step_original_of_enabled W hEnabled)

end shortCircuit

end Petri
end Pm4Lean
