import Pm4Lean.Models.Petri.Basic.Marking.Core

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

/-- Pointwise addition of markings. -/
def add (M N : Marking Place) : Marking Place :=
  fun p => M p + N p

/-- Pointwise natural subtraction of markings. -/
def sub (M N : Marking Place) : Marking Place :=
  fun p => M p - N p

/-- Scale every place of a marking by a natural number. -/
def scale (n : Nat) (M : Marking Place) : Marking Place :=
  fun p => n * M p

instance : Add (Marking Place) where
  add := add

instance : Sub (Marking Place) where
  sub := sub

theorem add_apply (M N : Marking Place) (p : Place) :
    (M + N) p = M p + N p := rfl

theorem sub_apply (M N : Marking Place) (p : Place) :
    (M - N) p = M p - N p := rfl

theorem scale_apply (n : Nat) (M : Marking Place) (p : Place) :
    scale n M p = n * M p := rfl

theorem add_zero (M : Marking Place) :
    M + zero = M := by
  apply ext
  intro p
  exact Nat.add_zero (M p)

theorem zero_add (M : Marking Place) :
    zero + M = M := by
  apply ext
  intro p
  exact Nat.zero_add (M p)

theorem scale_zero (M : Marking Place) :
    scale 0 M = zero := by
  apply ext
  intro p
  simp [scale, zero]

theorem sub_eq_zero_of_le {M N : Marking Place} (h : M ≤ N) :
    M - N = zero := by
  apply ext
  intro p
  exact Nat.sub_eq_zero_of_le (h p)

theorem add_sub_of_le {M N : Marking Place} (h : M ≤ N) :
    M + (N - M) = N := by
  apply ext
  intro p
  exact Nat.add_sub_of_le (h p)

theorem add_le_add {M₁ M₂ N₁ N₂ : Marking Place}
    (hM : M₁ ≤ M₂) (hN : N₁ ≤ N₂) :
    M₁ + N₁ ≤ M₂ + N₂ :=
  fun p => Nat.add_le_add (hM p) (hN p)

end Marking
end Petri
end Pm4Lean
