import Pm4Lean.Util.NatListOrder

namespace Pm4Lean

/-- All natural-number lists of length `n` whose entries are bounded by `k`. -/
def NatListsUpTo : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, k =>
      (List.range (k + 1)).flatMap
        (fun x => (NatListsUpTo n k).map (fun xs => x :: xs))

theorem mem_natListsUpTo_iff {n k : Nat} {xs : List Nat} :
    xs ∈ NatListsUpTo n k ↔
      xs.length = n ∧ ∀ x : Nat, x ∈ xs → x ≤ k := by
  induction n generalizing xs with
  | zero =>
      constructor
      · intro hMem
        simp [NatListsUpTo] at hMem
        subst xs
        exact ⟨rfl, by
          intro x hMem
          cases hMem⟩
      · intro h
        have hNil : xs = [] := List.eq_nil_of_length_eq_zero h.1
        subst hNil
        simp [NatListsUpTo]
  | succ n ih =>
      constructor
      · intro hMem
        rw [NatListsUpTo, List.mem_flatMap] at hMem
        obtain ⟨x, hXRange, hXMem⟩ := hMem
        rw [List.mem_map] at hXMem
        obtain ⟨ys, hYsMem, hEq⟩ := hXMem
        subst xs
        obtain ⟨hYsLen, hYsBound⟩ := ih.mp hYsMem
        exact ⟨by simp [hYsLen], by
          intro y hMem
          cases hMem with
          | head =>
              exact Nat.lt_succ_iff.mp
                ((List.mem_range).mp (by simpa using hXRange))
          | tail _ hTail =>
              exact hYsBound y hTail⟩
      · intro h
        cases xs with
        | nil =>
            cases h.1
        | cons x ys =>
            rw [NatListsUpTo, List.mem_flatMap]
            refine ⟨x, ?_, ?_⟩
            · rw [List.mem_range, Nat.lt_succ_iff]
              exact h.2 x (List.Mem.head ys)
            · rw [List.mem_map]
              refine ⟨ys, ?_, rfl⟩
              apply ih.mpr
              constructor
              · exact Nat.succ.inj h.1
              · intro y hYMem
                exact h.2 y (List.Mem.tail x hYMem)

end Pm4Lean
