import Pm4Lean.Models.Petri.Basic.Marking.FiniteOrder
import Pm4Lean.Util.NatListMax

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

/-- Read a marking as a finite vector over a chosen list of places. -/
def valuesOn (places : List Place) (M : Marking Place) : List Nat :=
  places.map M

/-- Read a net marking as coordinates over the net's stored place list. -/
def placeValues (N : Net) (M : N.Marking) : List Nat :=
  valuesOn N.places M

theorem valuesOn_length (places : List Place) (M : Marking Place) :
    (valuesOn places M).length = places.length := by
  simp [valuesOn]

theorem placeValues_length (N : Net) (M : N.Marking) :
    (placeValues N M).length = N.places.length := by
  simp [placeValues, valuesOn]

theorem mem_valuesOn_of_mem {places : List Place} {M : Marking Place}
    {p : Place} (hMem : p ∈ places) :
    M p ∈ valuesOn places M :=
  List.mem_map.mpr ⟨p, hMem, rfl⟩

theorem exists_place_of_mem_valuesOn {places : List Place}
    {M : Marking Place} {n : Nat}
    (hMem : n ∈ valuesOn places M) :
    ∃ p : Place, p ∈ places ∧ n = M p := by
  rw [valuesOn, List.mem_map] at hMem
  obtain ⟨p, hPlaceMem, hEq⟩ := hMem
  exact ⟨p, hPlaceMem, hEq.symm⟩

theorem exists_place_of_mem_placeValues
    (N : Net) {M : N.Marking} {n : Nat}
    (hMem : n ∈ placeValues N M) :
    ∃ p : N.Place, n = M p := by
  obtain ⟨p, _hPlaceMem, hEq⟩ :=
    exists_place_of_mem_valuesOn (places := N.places) hMem
  exact ⟨p, hEq⟩

theorem value_le_natListMax_placeValues
    (N : Net) (M : N.Marking) (p : N.Place) :
    M p ≤ NatListMax (placeValues N M) :=
  le_natListMax_of_mem
    (mem_valuesOn_of_mem (M := M) (N.places_complete p))

end Marking
end Petri
end Pm4Lean
