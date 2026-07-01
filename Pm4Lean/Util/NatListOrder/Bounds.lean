import Pm4Lean.Util.NatListMax
import Pm4Lean.Util.NatListOrder.Core

namespace Pm4Lean

theorem forall_le_of_mem_subset_natListMax_le {xs ys : List Nat} {k : Nat}
    (hMem : ∀ x : Nat, x ∈ xs → x ∈ ys)
    (hBound : NatListMax ys ≤ k) :
    ∀ x : Nat, x ∈ xs → x ≤ k := by
  intro x hx
  exact Nat.le_trans (le_natListMax_of_mem (hMem x hx)) hBound

theorem forall_le_natListMax_of_natListLe {xs ys : List Nat}
    (hLe : NatListLe xs ys) :
    ∀ x : Nat, x ∈ xs → x ≤ NatListMax ys := by
  induction xs generalizing ys with
  | nil =>
      intro x hMem
      cases hMem
  | cons y xs ih =>
      cases ys with
      | nil =>
          cases hLe
      | cons z ys =>
          intro x hMem
          cases hMem with
          | head =>
              exact Nat.le_trans hLe.1 (Nat.le_max_left z (NatListMax ys))
          | tail _ hTail =>
              exact Nat.le_trans
                (ih hLe.2 x hTail)
                (Nat.le_max_right z (NatListMax ys))

end Pm4Lean
