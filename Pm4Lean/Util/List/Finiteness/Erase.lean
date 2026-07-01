namespace Pm4Lean

namespace List

theorem mem_erase_of_ne_of_mem
    {α : Type u} [BEq α] [LawfulBEq α]
    {a b : α} {xs : List α}
    (hNe : a ≠ b) (hMem : a ∈ xs) :
    a ∈ xs.erase b := by
  induction xs with
  | nil =>
      cases hMem
  | cons x xs ih =>
      rw [List.erase_cons]
      by_cases hXB : (x == b) = true
      · simp [hXB]
        cases hMem with
        | head =>
            exact False.elim (hNe (LawfulBEq.eq_of_beq hXB))
        | tail _ hTail =>
            exact hTail
      · simp [hXB]
        cases hMem with
        | head =>
            exact Or.inl rfl
        | tail _ hTail =>
            exact Or.inr (ih hTail)

end List
end Pm4Lean
