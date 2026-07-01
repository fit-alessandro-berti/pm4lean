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

end Marking
end Petri
end Pm4Lean
