import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Lift

namespace Pm4Lean

theorem exists_indexSelection_ordered_head_tail_of_arbitrarily_large
    {f : Nat → List Nat} {headSeq : Nat → Nat} {tailSeq : Nat → List Nat}
    (hEq : ∀ i : Nat, f i = headSeq i :: tailSeq i)
    (hLarge :
      ∀ start bound : Nat, ∃ i : Nat, start ≤ i ∧ bound < headSeq i) :
    ∃ select : Nat → Nat,
      ∃ selectedHead : Nat → Nat,
        ∃ selectedTail : Nat → List Nat,
          (∀ i j : Nat, i < j → select i < select j) ∧
            (∀ i : Nat,
              f (select i) = selectedHead i :: selectedTail i) ∧
            (∀ i j : Nat, i < j → selectedHead i ≤ selectedHead j) ∧
            (∀ i : Nat, selectedHead i = headSeq (select i)) ∧
            (∀ i : Nat, selectedTail i = tailSeq (select i)) := by
  obtain ⟨select, hSelect, hHeadLt⟩ :=
    exists_indexSelection_of_arbitrarily_large hLarge
  refine ⟨select, fun i => headSeq (select i),
    fun i => tailSeq (select i), hSelect, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hEq (select i)
  · intro i j hLt
    exact Nat.le_of_lt (hHeadLt i j hLt)
  · intro i
    rfl
  · intro i
    rfl

end Pm4Lean
