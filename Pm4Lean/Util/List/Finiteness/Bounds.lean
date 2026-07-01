import Pm4Lean.Util.List.Finiteness.Erase

namespace Pm4Lean

namespace List

theorem length_le_length_of_nodup_subset
    {α : Type u} [BEq α] [LawfulBEq α]
    {xs univList : List α}
    (hNodup : xs.Nodup)
    (hSubset : ∀ a : α, a ∈ xs → a ∈ univList) :
    xs.length ≤ univList.length := by
  induction xs generalizing univList with
  | nil =>
      exact Nat.zero_le univList.length
  | cons x xs ih =>
      obtain ⟨hXNotMem, hXsNodup⟩ := List.nodup_cons.mp hNodup
      have hXMem : x ∈ univList := hSubset x (List.Mem.head xs)
      have hXsSubsetErase :
          ∀ a : α, a ∈ xs → a ∈ univList.erase x := by
        intro a hAMem
        apply mem_erase_of_ne_of_mem
        · intro hEq
          subst hEq
          exact hXNotMem hAMem
        · exact hSubset a (List.Mem.tail x hAMem)
      have hLenErase : xs.length ≤ (univList.erase x).length :=
        ih hXsNodup hXsSubsetErase
      cases univList with
      | nil =>
          cases hXMem
      | cons u us =>
          have hEraseLen : ((u :: us).erase x).length = us.length := by
            have hLen := List.length_erase_of_mem hXMem
            simpa using hLen
          exact Nat.succ_le_succ (by
            simpa [hEraseLen] using hLenErase)

theorem not_nodup_of_length_gt_length_of_subset
    {α : Type u} [BEq α] [LawfulBEq α]
    {xs univList : List α}
    (hLen : univList.length < xs.length)
    (hSubset : ∀ a : α, a ∈ xs → a ∈ univList) :
    ¬ xs.Nodup := by
  intro hNodup
  exact Nat.not_lt_of_ge
    (length_le_length_of_nodup_subset hNodup hSubset)
    hLen

end List
end Pm4Lean
