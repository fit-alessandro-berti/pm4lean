namespace Pm4Lean
namespace Petri

/-- A Petri-net marking assigns a natural number of tokens to every place. -/
abbrev Marking (Place : Type u) := Place → Nat

namespace Marking

variable {Place : Type u}

/-- The empty marking. -/
def zero : Marking Place := fun _ => 0

/-- A marking with one token in a single place. -/
def singleton [DecidableEq Place] (p : Place) : Marking Place :=
  fun q => if q = p then 1 else 0

/-- Pointwise order on markings. -/
def le (M N : Marking Place) : Prop :=
  ∀ p, M p ≤ N p

instance : LE (Marking Place) where
  le := le

theorem le_def {M N : Marking Place} :
    M ≤ N ↔ ∀ p, M p ≤ N p := Iff.rfl

theorem le_refl (M : Marking Place) : M ≤ M :=
  fun _ => Nat.le_refl _

theorem le_trans {M N K : Marking Place} (hMN : M ≤ N) (hNK : N ≤ K) :
    M ≤ K :=
  fun p => Nat.le_trans (hMN p) (hNK p)

theorem exists_lt_of_le_ne {M N : Marking Place} (hLe : M ≤ N)
    (hNe : M ≠ N) :
    ∃ p : Place, M p < N p := by
  classical
  by_cases hExists : ∃ p : Place, M p < N p
  · exact hExists
  · exact False.elim (hNe (by
      apply funext
      intro p
      exact Nat.le_antisymm (hLe p)
        (Nat.le_of_not_gt (by
          intro hLt
          exact hExists ⟨p, hLt⟩))))

theorem ext {M N : Marking Place} (h : ∀ p, M p = N p) : M = N :=
  funext h

theorem zero_apply (p : Place) : (zero : Marking Place) p = 0 := rfl

theorem singleton_self [DecidableEq Place] (p : Place) :
    singleton p p = 1 := by
  simp [singleton]

theorem singleton_other [DecidableEq Place] {p q : Place} (h : q ≠ p) :
    singleton p q = 0 := by
  simp [singleton, h]

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
