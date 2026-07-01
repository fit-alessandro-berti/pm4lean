import Pm4Lean.Util.List.Duplicate.Nodup

namespace Pm4Lean

namespace List

theorem hasDuplicate_of_not_nodup
    {α : Type u} {xs : List α}
    (hNotNodup : ¬ xs.Nodup) :
    HasDuplicate xs := by
  classical
  induction xs with
  | nil =>
      exact False.elim (hNotNodup List.nodup_nil)
  | cons x xs ih =>
      by_cases hMem : x ∈ xs
      · exact Or.inl hMem
      · exact Or.inr (ih (by
          intro hXsNodup
          exact hNotNodup
            (List.nodup_cons.mpr ⟨hMem, hXsNodup⟩)))

theorem containsDuplicatePair_of_hasDuplicate
    {α : Type u} {xs : List α}
    (hDuplicate : HasDuplicate xs) :
    ContainsDuplicatePair xs := by
  induction xs with
  | nil =>
      exact False.elim hDuplicate
  | cons x xs ih =>
      unfold HasDuplicate at hDuplicate
      cases hDuplicate with
      | inl hMem =>
          obtain ⟨between, after, hSplit⟩ := exists_split_of_mem hMem
          exact ⟨x, [], between, after, by simp [hSplit]⟩
      | inr hTail =>
          obtain ⟨a, before, between, after, hSplit⟩ := ih hTail
          exact ⟨a, x :: before, between, after, by simp [hSplit]⟩

theorem containsDuplicatePair_of_not_nodup
    {α : Type u} {xs : List α}
    (hNotNodup : ¬ xs.Nodup) :
    ContainsDuplicatePair xs :=
  containsDuplicatePair_of_hasDuplicate
    (hasDuplicate_of_not_nodup hNotNodup)

theorem not_nodup_iff_containsDuplicatePair
    {α : Type u} {xs : List α} :
    ¬ xs.Nodup ↔ ContainsDuplicatePair xs :=
  ⟨containsDuplicatePair_of_not_nodup,
    not_nodup_of_containsDuplicatePair⟩

end List
end Pm4Lean
