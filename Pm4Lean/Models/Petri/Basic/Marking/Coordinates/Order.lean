import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Core
import Pm4Lean.Util.NatListOrder

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

theorem valuesOn_le_of_forall_mem {places : List Place}
    {M M' : Marking Place}
    (hLe : ∀ p : Place, p ∈ places → M p ≤ M' p) :
    NatListLe (valuesOn places M) (valuesOn places M') := by
  induction places with
  | nil =>
      trivial
  | cons p places ih =>
      exact ⟨hLe p (List.Mem.head places),
        ih (by
          intro q hMem
          exact hLe q (List.Mem.tail p hMem))⟩

theorem forall_mem_of_valuesOn_le {places : List Place}
    {M M' : Marking Place}
    (hLe : NatListLe (valuesOn places M) (valuesOn places M')) :
    ∀ p : Place, p ∈ places → M p ≤ M' p := by
  induction places with
  | nil =>
      intro p hMem
      cases hMem
  | cons q places ih =>
      intro p hMem
      cases hMem with
      | head =>
          exact hLe.1
      | tail _ hTail =>
          exact ih hLe.2 p hTail

theorem placeValues_le_of_le
    {N : Net} {M M' : N.Marking} (hLe : M ≤ M') :
    NatListLe (placeValues N M) (placeValues N M') :=
  valuesOn_le_of_forall_mem (forall_mem_of_le (N := N) hLe)

theorem le_of_placeValues_le
    {N : Net} {M M' : N.Marking}
    (hLe : NatListLe (placeValues N M) (placeValues N M')) :
    M ≤ M' :=
  le_of_forall_mem (N := N)
    (forall_mem_of_valuesOn_le hLe)

theorem le_iff_placeValues_le
    {N : Net} {M M' : N.Marking} :
    M ≤ M' ↔ NatListLe (placeValues N M) (placeValues N M') :=
  ⟨placeValues_le_of_le, le_of_placeValues_le⟩

theorem eq_of_placeValues_eq
    {N : Net} {M M' : N.Marking}
    (hEq : placeValues N M = placeValues N M') :
    M = M' := by
  apply ext
  intro p
  have hLe : M ≤ M' := by
    apply le_of_placeValues_le
    rw [hEq]
    exact natListLe_refl (placeValues N M')
  have hGe : M' ≤ M := by
    apply le_of_placeValues_le
    rw [hEq]
    exact natListLe_refl (placeValues N M')
  exact Nat.le_antisymm (hLe p) (hGe p)

theorem placeValues_eq_of_eq
    {N : Net} {M M' : N.Marking}
    (hEq : M = M') :
    placeValues N M = placeValues N M' := by
  subst hEq
  rfl

theorem eq_iff_placeValues_eq
    {N : Net} {M M' : N.Marking} :
    M = M' ↔ placeValues N M = placeValues N M' :=
  ⟨placeValues_eq_of_eq, eq_of_placeValues_eq⟩

theorem eq_of_placeValues_le_le
    {N : Net} {M M' : N.Marking}
    (hLe : NatListLe (placeValues N M) (placeValues N M'))
    (hGe : NatListLe (placeValues N M') (placeValues N M)) :
    M = M' :=
  eq_of_placeValues_eq (natListLe_antisymm hLe hGe)

end Marking
end Petri
end Pm4Lean
