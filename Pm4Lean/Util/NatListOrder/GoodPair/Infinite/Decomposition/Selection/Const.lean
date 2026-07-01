import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Lift

namespace Pm4Lean

theorem exists_indexSelection_const_head_tail_of_frequently_eq
    {f : Nat → List Nat} {headSeq : Nat → Nat} {tailSeq : Nat → List Nat}
    {value : Nat}
    (hEq : ∀ i : Nat, f i = headSeq i :: tailSeq i)
    (hFrequent :
      ∀ start : Nat, ∃ i : Nat, start ≤ i ∧ headSeq i = value) :
    ∃ select : Nat → Nat,
      ∃ selectedTail : Nat → List Nat,
        (∀ i j : Nat, i < j → select i < select j) ∧
          (∀ i : Nat, f (select i) = value :: selectedTail i) ∧
          (∀ i : Nat, selectedTail i = tailSeq (select i)) := by
  obtain ⟨select, hSelect, hValue⟩ :=
    exists_indexSelection_of_frequently_eq hFrequent
  refine ⟨select, fun i => tailSeq (select i), hSelect, ?_, ?_⟩
  · intro i
    rw [hEq (select i), hValue i]
  · intro i
    rfl

end Pm4Lean
