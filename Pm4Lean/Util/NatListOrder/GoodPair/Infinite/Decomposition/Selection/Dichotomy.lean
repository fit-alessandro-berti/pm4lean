import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Selection.Const
import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Selection.Ordered

namespace Pm4Lean

theorem exists_indexSelection_const_or_ordered_head_tail
    {f : Nat → List Nat} {headSeq : Nat → Nat} {tailSeq : Nat → List Nat}
    (hEq : ∀ i : Nat, f i = headSeq i :: tailSeq i) :
    (∃ value : Nat,
      ∃ select : Nat → Nat,
        ∃ selectedTail : Nat → List Nat,
          (∀ i j : Nat, i < j → select i < select j) ∧
            (∀ i : Nat, f (select i) = value :: selectedTail i) ∧
            (∀ i : Nat, selectedTail i = tailSeq (select i))) ∨
      (∃ select : Nat → Nat,
        ∃ selectedHead : Nat → Nat,
          ∃ selectedTail : Nat → List Nat,
            (∀ i j : Nat, i < j → select i < select j) ∧
              (∀ i : Nat,
                f (select i) = selectedHead i :: selectedTail i) ∧
              (∀ i j : Nat, i < j → selectedHead i ≤ selectedHead j) ∧
              (∀ i : Nat, selectedHead i = headSeq (select i)) ∧
              (∀ i : Nat, selectedTail i = tailSeq (select i))) := by
  obtain hFrequent | hLarge :=
    exists_frequent_eq_or_arbitrarily_large headSeq
  · obtain ⟨value, hValueFrequent⟩ := hFrequent
    obtain ⟨select, selectedTail, hSelect, hSelectedEq, hTailEq⟩ :=
      exists_indexSelection_const_head_tail_of_frequently_eq
        hEq hValueFrequent
    exact Or.inl
      ⟨value, select, selectedTail, hSelect, hSelectedEq, hTailEq⟩
  · exact Or.inr
      (exists_indexSelection_ordered_head_tail_of_arbitrarily_large
        hEq hLarge)

end Pm4Lean
