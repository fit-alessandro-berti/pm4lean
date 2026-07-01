import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Box

namespace Pm4Lean
namespace Petri

namespace Marking

theorem placeValues_list_mem_natListsUpTo_of_forall_le
    {N : Net} {markings : List N.Marking} {k : Nat}
    (hBound : ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    ∀ coords : List Nat,
      coords ∈ markings.map (placeValues N) →
        coords ∈ NatListsUpTo N.places.length k := by
  intro coords hMem
  rw [List.mem_map] at hMem
  obtain ⟨M, hMMem, hEq⟩ := hMem
  subst coords
  exact placeValues_mem_natListsUpTo_of_forall_le (hBound M hMMem)

theorem not_nodup_placeValues_of_length_gt_natListsUpTo_length
    {N : Net} {markings : List N.Marking} {k : Nat}
    (hLength :
      (NatListsUpTo N.places.length k).length <
        (markings.map (placeValues N)).length)
    (hBound : ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    ¬ (markings.map (placeValues N)).Nodup :=
  not_nodup_of_length_gt_natListsUpTo_length hLength
    (placeValues_list_mem_natListsUpTo_of_forall_le hBound)

theorem nodup_placeValues_of_nodup
    {N : Net} {markings : List N.Marking}
    (hNodup : markings.Nodup) :
    (markings.map (placeValues N)).Nodup :=
  Pm4Lean.List.nodup_map_of_injective
    (fun _M _M' hEq => eq_of_placeValues_eq hEq)
    hNodup

theorem length_le_natListsUpTo_length_of_nodup_markings_forall_le
    {N : Net} {markings : List N.Marking} {k : Nat}
    (hNodup : markings.Nodup)
    (hBound : ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    markings.length ≤ (NatListsUpTo N.places.length k).length := by
  have hMapBound :
      (markings.map (placeValues N)).length ≤
        (NatListsUpTo N.places.length k).length :=
    length_le_natListsUpTo_length_of_nodup
      (nodup_placeValues_of_nodup hNodup)
      (placeValues_list_mem_natListsUpTo_of_forall_le hBound)
  simpa [List.length_map] using hMapBound

theorem not_nodup_markings_of_length_gt_natListsUpTo_length
    {N : Net} {markings : List N.Marking} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < markings.length)
    (hBound : ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    ¬ markings.Nodup := by
  intro hNodup
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_nodup_markings_forall_le
      hNodup hBound)
    hLength

theorem hasDuplicate_markings_of_length_gt_natListsUpTo_length
    {N : Net} {markings : List N.Marking} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < markings.length)
    (hBound : ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    List.HasDuplicate markings :=
  Pm4Lean.List.hasDuplicate_of_not_nodup
    (not_nodup_markings_of_length_gt_natListsUpTo_length
      hLength hBound)

end Marking
end Petri
end Pm4Lean
