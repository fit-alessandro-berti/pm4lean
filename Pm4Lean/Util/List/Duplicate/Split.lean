namespace Pm4Lean

namespace List

theorem exists_split_of_mem
    {α : Type u} {a : α} {xs : List α}
    (hMem : a ∈ xs) :
    ∃ before after : List α, xs = before ++ a :: after := by
  induction xs with
  | nil =>
      cases hMem
  | cons x xs ih =>
      cases hMem with
      | head =>
          exact ⟨[], xs, rfl⟩
      | tail _ hTail =>
          obtain ⟨before, after, hEq⟩ := ih hTail
          exact ⟨x :: before, after, by simp [hEq]⟩

end List
end Pm4Lean
