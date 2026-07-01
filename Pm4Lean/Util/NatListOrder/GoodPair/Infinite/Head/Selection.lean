import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Head.Dichotomy

namespace Pm4Lean

theorem exists_indexSelection_of_frequently_eq
    {head : Nat → Nat} {value : Nat}
    (hFrequent :
      ∀ start : Nat, ∃ i : Nat, start ≤ i ∧ head i = value) :
    ∃ select : Nat → Nat,
      (∀ i j : Nat, i < j → select i < select j) ∧
        ∀ i : Nat, head (select i) = value := by
  classical
  let select : Nat → Nat := fun n =>
    Nat.recOn n
      (Classical.choose (hFrequent 0))
      (fun _ previous => Classical.choose (hFrequent (previous + 1)))
  have hValue : ∀ i : Nat, head (select i) = value := by
    intro i
    cases i with
    | zero =>
        exact (Classical.choose_spec (hFrequent 0)).2
    | succ i =>
        exact (Classical.choose_spec (hFrequent (select i + 1))).2
  have hStep : ∀ i : Nat, select i < select (i + 1) := by
    intro i
    exact Nat.lt_of_succ_le
      (by
        simpa [select] using
          (Classical.choose_spec (hFrequent (select i + 1))).1)
  exact ⟨select, indexSelection_strict_of_step hStep, hValue⟩

theorem exists_indexSelection_of_arbitrarily_large
    {head : Nat → Nat}
    (hLarge :
      ∀ start bound : Nat, ∃ i : Nat, start ≤ i ∧ bound < head i) :
    ∃ select : Nat → Nat,
      (∀ i j : Nat, i < j → select i < select j) ∧
        ∀ i j : Nat, i < j → head (select i) < head (select j) := by
  classical
  let select : Nat → Nat := fun n =>
    Nat.recOn n
      (Classical.choose (hLarge 0 0))
      (fun _ previous =>
        Classical.choose (hLarge (previous + 1) (head previous)))
  have hIndexStep : ∀ i : Nat, select i < select (i + 1) := by
    intro i
    exact Nat.lt_of_succ_le
      (by
        simpa [select] using
          (Classical.choose_spec
            (hLarge (select i + 1) (head (select i)))).1)
  have hHeadStep : ∀ i : Nat, head (select i) < head (select (i + 1)) := by
    intro i
    simpa [select] using
      (Classical.choose_spec
        (hLarge (select i + 1) (head (select i)))).2
  exact ⟨select,
    indexSelection_strict_of_step hIndexStep,
    natSequence_strict_of_step hHeadStep⟩

end Pm4Lean
