import Pm4Lean.Util.NatListBox.Basic.Definition

namespace Pm4Lean

theorem mem_natListsUpTo
    {n k : Nat} {xs : List Nat}
    (hLength : xs.length = n)
    (hBound : ∀ x : Nat, x ∈ xs → x ≤ k) :
    xs ∈ NatListsUpTo n k :=
  mem_natListsUpTo_iff.mpr ⟨hLength, hBound⟩

theorem length_eq_of_mem_natListsUpTo
    {n k : Nat} {xs : List Nat}
    (hMem : xs ∈ NatListsUpTo n k) :
    xs.length = n :=
  (mem_natListsUpTo_iff.mp hMem).1

theorem forall_le_of_mem_natListsUpTo
    {n k : Nat} {xs : List Nat}
    (hMem : xs ∈ NatListsUpTo n k) :
    ∀ x : Nat, x ∈ xs → x ≤ k :=
  (mem_natListsUpTo_iff.mp hMem).2

end Pm4Lean
