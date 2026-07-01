import Pm4Lean.Util.NatListOrder.GoodPair.Base.Head.Member

namespace Pm4Lean

theorem forall_cons_head_lt_of_forall_tail_natListLe_of_not_containsNatListLePair_cons
    {x : Nat} {xs : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hTailLe : ∀ vector : List Nat, vector ∈ vectors →
      ∃ y : Nat, ∃ ys : List Nat,
        vector = y :: ys ∧ NatListLe xs ys) :
    ∀ vector : List Nat, vector ∈ vectors →
      ∃ y : Nat, ∃ ys : List Nat,
        vector = y :: ys ∧ y < x := by
  intro vector hMem
  exact
    exists_cons_head_lt_of_mem_tail_natListLe_of_not_containsNatListLePair_cons
      hNoPair hMem (hTailLe vector hMem)

theorem forall_cons_head_le_of_forall_tail_natListLe_of_not_containsNatListLePair_cons
    {x : Nat} {xs : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hTailLe : ∀ vector : List Nat, vector ∈ vectors →
      ∃ y : Nat, ∃ ys : List Nat,
        vector = y :: ys ∧ NatListLe xs ys) :
    ∀ vector : List Nat, vector ∈ vectors →
      ∃ y : Nat, ∃ ys : List Nat,
        vector = y :: ys ∧ y ≤ x := by
  intro vector hMem
  exact
    exists_cons_head_le_of_mem_tail_natListLe_of_not_containsNatListLePair_cons
      hNoPair hMem (hTailLe vector hMem)

end Pm4Lean
