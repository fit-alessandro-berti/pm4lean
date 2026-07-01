import Pm4Lean.Util.NatListOrder.GoodPair.Base.Core

namespace Pm4Lean

theorem not_head_le_of_tail_natListLe_of_not_containsNatListLePair_cons
    {x y : Nat} {xs ys : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hMem : y :: ys ∈ vectors)
    (hTailLe : NatListLe xs ys) :
    ¬ x ≤ y := by
  intro hHeadLe
  exact not_natListLe_head_of_not_containsNatListLePair_cons
    hNoPair hMem
    (natListLe_cons hHeadLe hTailLe)

theorem head_lt_of_tail_natListLe_of_not_containsNatListLePair_cons
    {x y : Nat} {xs ys : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hMem : y :: ys ∈ vectors)
    (hTailLe : NatListLe xs ys) :
    y < x :=
  Nat.lt_of_not_ge
    (not_head_le_of_tail_natListLe_of_not_containsNatListLePair_cons
      hNoPair hMem hTailLe)

theorem exists_cons_head_lt_of_mem_tail_natListLe_of_not_containsNatListLePair_cons
    {x : Nat} {xs vector : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hMem : vector ∈ vectors)
    (hTailLe : ∃ y : Nat, ∃ ys : List Nat,
      vector = y :: ys ∧ NatListLe xs ys) :
    ∃ y : Nat, ∃ ys : List Nat,
      vector = y :: ys ∧ y < x := by
  obtain ⟨y, ys, hVectorEq, hLe⟩ := hTailLe
  subst hVectorEq
  exact ⟨y, ys, rfl,
    head_lt_of_tail_natListLe_of_not_containsNatListLePair_cons
      hNoPair hMem hLe⟩

theorem exists_cons_head_le_of_mem_tail_natListLe_of_not_containsNatListLePair_cons
    {x : Nat} {xs vector : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ((x :: xs) :: vectors))
    (hMem : vector ∈ vectors)
    (hTailLe : ∃ y : Nat, ∃ ys : List Nat,
      vector = y :: ys ∧ NatListLe xs ys) :
    ∃ y : Nat, ∃ ys : List Nat,
      vector = y :: ys ∧ y ≤ x := by
  obtain ⟨y, ys, hVectorEq, hLt⟩ :=
    exists_cons_head_lt_of_mem_tail_natListLe_of_not_containsNatListLePair_cons
      hNoPair hMem hTailLe
  exact ⟨y, ys, hVectorEq, Nat.le_of_lt hLt⟩

end Pm4Lean
