import Pm4Lean.Models.Petri.Basic.Net

namespace Pm4Lean
namespace Petri

namespace Marking

theorem le_of_forall_mem
    {N : Net} {M M' : N.Marking}
    (hLe : ∀ p : N.Place, p ∈ N.places → M p ≤ M' p) :
    M ≤ M' :=
  fun p => hLe p (N.places_complete p)

theorem forall_mem_of_le
    {N : Net} {M M' : N.Marking}
    (hLe : M ≤ M') :
    ∀ p : N.Place, p ∈ N.places → M p ≤ M' p :=
  fun p _hMem => hLe p

theorem eq_of_forall_mem
    {N : Net} {M M' : N.Marking}
    (hEq : ∀ p : N.Place, p ∈ N.places → M p = M' p) :
    M = M' := by
  apply ext
  intro p
  exact hEq p (N.places_complete p)

theorem exists_mem_lt_of_le_ne
    {N : Net} {M M' : N.Marking}
    (hLe : M ≤ M') (hNe : M ≠ M') :
    ∃ p : N.Place, p ∈ N.places ∧ M p < M' p := by
  obtain ⟨p, hLt⟩ := exists_lt_of_le_ne hLe hNe
  exact ⟨p, N.places_complete p, hLt⟩

theorem not_le_iff_exists_mem_gt
    {N : Net} {M M' : N.Marking} :
    ¬ M ≤ M' ↔
      ∃ p : N.Place, p ∈ N.places ∧ M' p < M p := by
  constructor
  · intro hNotLe
    by_cases hExists :
        ∃ p : N.Place, p ∈ N.places ∧ M' p < M p
    · exact hExists
    · exact False.elim (hNotLe (le_of_forall_mem (N := N) (by
        intro p hMem
        exact Nat.le_of_not_gt (by
          intro hLt
          exact hExists ⟨p, hMem, hLt⟩))))
  · intro hExists hLe
    obtain ⟨p, _hMem, hGt⟩ := hExists
    exact Nat.not_lt_of_ge (hLe p) hGt

end Marking
end Petri
end Pm4Lean
