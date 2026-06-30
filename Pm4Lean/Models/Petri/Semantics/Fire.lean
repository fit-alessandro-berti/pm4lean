import Pm4Lean.Models.Petri.Semantics.Enabled

namespace Pm4Lean
namespace Petri

/-- The marking obtained by firing a transition. -/
def fire (N : Net) (M : N.Marking) (t : N.Transition) : N.Marking :=
  M - N.pre t + N.post t

theorem fire_apply (N : Net) (M : N.Marking) (t : N.Transition) (p : N.Place) :
    fire N M t p = M p - N.pre t p + N.post t p := rfl

theorem fire_preserves_nonnegativity
    (N : Net) (M : N.Marking) (t : N.Transition) (p : N.Place) :
    0 ≤ fire N M t p :=
  Nat.zero_le _

theorem fire_token_eq_of_no_pre
    {N : Net} {M : N.Marking} {t : N.Transition} {p : N.Place}
    (h : N.pre t p = 0) :
    fire N M t p = M p + N.post t p := by
  calc
    fire N M t p = M p - N.pre t p + N.post t p := rfl
    _ = M p - 0 + N.post t p := by rw [h]
    _ = M p + N.post t p := by rw [Nat.sub_zero]

theorem fire_token_monotone_of_no_pre
    {N : Net} {M : N.Marking} {t : N.Transition} {p : N.Place}
    (h : N.pre t p = 0) :
    M p ≤ fire N M t p := by
  rw [fire_token_eq_of_no_pre h]
  exact Nat.le_add_right (M p) (N.post t p)

end Petri
end Pm4Lean
