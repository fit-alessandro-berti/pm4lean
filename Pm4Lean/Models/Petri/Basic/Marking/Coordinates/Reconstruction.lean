import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Order

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u} [DecidableEq Place]

/--
Build a marking from coordinates over a place list.  Extra coordinates are
ignored and missing coordinates default to zero.
-/
def ofValuesOn : List Place → List Nat → Marking Place
  | [], _ => zero
  | p :: ps, [] => fun q => if q = p then 0 else ofValuesOn ps [] q
  | p :: ps, n :: ns => fun q => if q = p then n else ofValuesOn ps ns q

theorem ofValuesOn_valuesOn_eq_of_mem {places : List Place}
    (M : Marking Place) :
    ∀ p : Place, p ∈ places →
      ofValuesOn places (valuesOn places M) p = M p := by
  induction places with
  | nil =>
      intro p hMem
      cases hMem
  | cons q places ih =>
      intro p hMem
      cases hMem with
      | head =>
          simp [ofValuesOn, valuesOn]
      | tail _ hTail =>
          by_cases hEq : p = q
          · subst hEq
            simp [ofValuesOn, valuesOn]
          · simp [ofValuesOn, valuesOn, hEq]
            exact ih p hTail

theorem of_placeValues_eq
    (N : Net) (M : N.Marking) :
    ofValuesOn N.places (placeValues N M) = M := by
  apply ext
  intro p
  exact ofValuesOn_valuesOn_eq_of_mem
    M p (N.places_complete p)

theorem valuesOn_le_of_natListLe_ofValuesOn
    {places : List Place} {M : Marking Place} {coords : List Nat}
    (hLe : NatListLe (valuesOn places M) coords) :
    ∀ p : Place, p ∈ places → M p ≤ ofValuesOn places coords p := by
  induction places generalizing coords with
  | nil =>
      intro p hMem
      cases hMem
  | cons q places ih =>
      cases coords with
      | nil =>
          cases hLe
      | cons n coords =>
          intro p hMem
          cases hMem with
          | head =>
              simp [ofValuesOn]
              exact hLe.1
          | tail _ hTail =>
              by_cases hEq : p = q
              · subst hEq
                simp [ofValuesOn]
                exact hLe.1
              · simp [ofValuesOn, hEq]
                exact ih hLe.2 p hTail

theorem le_of_placeValues_le_coords
    (N : Net) {M : N.Marking} {coords : List Nat}
    (hLe : NatListLe (placeValues N M) coords) :
    M ≤ ofValuesOn N.places coords :=
  le_of_forall_mem (N := N)
    (valuesOn_le_of_natListLe_ofValuesOn hLe)

end Marking
end Petri
end Pm4Lean
