import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Reconstruction
import Pm4Lean.Util.NatListBox

namespace Pm4Lean
namespace Petri

namespace Marking

/-- All markings whose stored place coordinates are bounded by `k`. -/
def boundedPlaceValueMarkings (N : Net) (k : Nat) : List N.Marking :=
  (NatListsUpTo N.places.length k).map
    (fun coords => ofValuesOn N.places coords)

theorem placeValues_mem_natListsUpTo_of_forall_le
    {N : Net} {M : N.Marking} {k : Nat}
    (hBound : ∀ p : N.Place, M p ≤ k) :
    placeValues N M ∈ NatListsUpTo N.places.length k := by
  apply mem_natListsUpTo
  · simp [placeValues, valuesOn]
  · intro x hMem
    rw [placeValues, valuesOn, List.mem_map] at hMem
    obtain ⟨p, _hPMem, hEq⟩ := hMem
    subst x
    exact hBound p

theorem mem_boundedPlaceValueMarkings_of_forall_le
    {N : Net} {M : N.Marking} {k : Nat}
    (hBound : ∀ p : N.Place, M p ≤ k) :
    M ∈ boundedPlaceValueMarkings N k := by
  rw [boundedPlaceValueMarkings, List.mem_map]
  refine ⟨placeValues N M,
    placeValues_mem_natListsUpTo_of_forall_le hBound, ?_⟩
  exact of_placeValues_eq N M

theorem exists_mem_boundedPlaceValueMarkings_ge_of_forall_le
    {N : Net} {M : N.Marking} {k : Nat}
    (hBound : ∀ p : N.Place, M p ≤ k) :
    ∃ M' : N.Marking,
      M' ∈ boundedPlaceValueMarkings N k ∧ M ≤ M' := by
  exact ⟨M, mem_boundedPlaceValueMarkings_of_forall_le hBound,
    le_refl M⟩

theorem mem_boundedPlaceValueMarkings_ge_of_le
    {N : Net}
    {M M' : N.Marking} {k : Nat}
    (hMem : M' ∈ boundedPlaceValueMarkings N k)
    (hLe : M ≤ M') :
    ∃ M'' : N.Marking,
      M'' ∈ boundedPlaceValueMarkings N k ∧ M ≤ M'' :=
  ⟨M', hMem, hLe⟩

end Marking
end Petri
end Pm4Lean
