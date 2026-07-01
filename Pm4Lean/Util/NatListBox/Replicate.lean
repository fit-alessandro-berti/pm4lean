import Pm4Lean.Util.NatListBox.Basic

namespace Pm4Lean

theorem natListLe_replicate_of_length_forall_le
    {xs : List Nat} {n k : Nat}
    (hLength : xs.length = n)
    (hBound : ∀ x : Nat, x ∈ xs → x ≤ k) :
    NatListLe xs (List.replicate n k) := by
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero =>
          trivial
      | succ n =>
          cases hLength
  | cons x xs ih =>
      cases n with
      | zero =>
          cases hLength
      | succ n =>
          exact ⟨hBound x (List.Mem.head xs),
            ih (Nat.succ.inj hLength)
              (by
                intro y hYMem
                exact hBound y (List.Mem.tail x hYMem))⟩

theorem natListLe_replicate_of_mem_natListsUpTo
    {n k : Nat} {xs : List Nat}
    (hMem : xs ∈ NatListsUpTo n k) :
    NatListLe xs (List.replicate n k) :=
  natListLe_replicate_of_length_forall_le
    (length_eq_of_mem_natListsUpTo hMem)
    (forall_le_of_mem_natListsUpTo hMem)

end Pm4Lean
