import Pm4Lean.Models.Petri.Basic.Marking

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

/-- A marking has no tokens outside a finite list of places. -/
def EmptyOutside (places : List Place) (M : Marking Place) : Prop :=
  ∀ p : Place, p ∉ places → M p = 0

theorem emptyOutside_nil_iff (M : Marking Place) :
    EmptyOutside [] M ↔ M = zero := by
  constructor
  · intro h
    apply ext
    intro p
    exact h p (by simp)
  · intro h p _hp
    rw [h]
    rfl

theorem emptyOutside_of_subset {support allowed : List Place}
    {M : Marking Place}
    (hSubset : ∀ p : Place, p ∈ support → p ∈ allowed)
    (hEmpty : EmptyOutside support M) :
    EmptyOutside allowed M := by
  intro p hpNotInPlaces
  apply hEmpty
  intro hpInSupport
  exact hpNotInPlaces (hSubset p hpInSupport)

theorem emptyOutside_zero (places : List Place) :
    EmptyOutside places (zero : Marking Place) := by
  intro _p _h
  rfl

end Marking
end Petri
end Pm4Lean
