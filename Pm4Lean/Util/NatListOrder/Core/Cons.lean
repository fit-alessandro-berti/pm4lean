import Pm4Lean.Util.NatListOrder.Core.Order

namespace Pm4Lean

theorem natListLe_cons
    {x y : Nat} {xs ys : List Nat}
    (hHead : x ≤ y) (hTail : NatListLe xs ys) :
    NatListLe (x :: xs) (y :: ys) :=
  ⟨hHead, hTail⟩

theorem natListLe_head_of_cons
    {x y : Nat} {xs ys : List Nat}
    (hLe : NatListLe (x :: xs) (y :: ys)) :
    x ≤ y :=
  hLe.1

theorem natListLe_tail_of_cons
    {x y : Nat} {xs ys : List Nat}
    (hLe : NatListLe (x :: xs) (y :: ys)) :
    NatListLe xs ys :=
  hLe.2

theorem natListLe_cons_iff
    {x y : Nat} {xs ys : List Nat} :
    NatListLe (x :: xs) (y :: ys) ↔ x ≤ y ∧ NatListLe xs ys := by
  constructor
  · intro hLe
    exact ⟨natListLe_head_of_cons hLe, natListLe_tail_of_cons hLe⟩
  · intro h
    exact natListLe_cons h.1 h.2

end Pm4Lean
