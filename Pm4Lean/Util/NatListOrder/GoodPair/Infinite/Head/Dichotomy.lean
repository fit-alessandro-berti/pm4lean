import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Basic

namespace Pm4Lean

theorem eventually_gt_of_eventually_ne_each_value
    {head : Nat → Nat}
    (hRare :
      ∀ value : Nat, ∃ cutoff : Nat,
        ∀ i : Nat, cutoff ≤ i → head i ≠ value) :
    ∀ bound : Nat, ∃ cutoff : Nat,
      ∀ i : Nat, cutoff ≤ i → bound < head i := by
  intro bound
  induction bound with
  | zero =>
      obtain ⟨cutoff, hCutoff⟩ := hRare 0
      exact ⟨cutoff, by
        intro i hLe
        exact Nat.pos_of_ne_zero (hCutoff i hLe)⟩
  | succ bound ih =>
      obtain ⟨cutoffBound, hBound⟩ := ih
      obtain ⟨cutoffValue, hValue⟩ := hRare (bound + 1)
      refine ⟨max cutoffBound cutoffValue, ?_⟩
      intro i hLe
      have hCutoffBound : cutoffBound ≤ i :=
        Nat.le_trans (Nat.le_max_left cutoffBound cutoffValue) hLe
      have hCutoffValue : cutoffValue ≤ i :=
        Nat.le_trans (Nat.le_max_right cutoffBound cutoffValue) hLe
      have hSuccLe : bound + 1 ≤ head i :=
        Nat.succ_le_of_lt (hBound i hCutoffBound)
      exact Nat.lt_of_le_of_ne hSuccLe (hValue i hCutoffValue).symm

theorem exists_frequent_eq_or_arbitrarily_large
    (head : Nat → Nat) :
    (∃ value : Nat,
      ∀ start : Nat, ∃ i : Nat, start ≤ i ∧ head i = value) ∨
      (∀ start bound : Nat,
        ∃ i : Nat, start ≤ i ∧ bound < head i) := by
  classical
  by_cases hFrequent :
      ∃ value : Nat,
        ∀ start : Nat, ∃ i : Nat, start ≤ i ∧ head i = value
  · exact Or.inl hFrequent
  · right
    have hRare :
        ∀ value : Nat, ∃ cutoff : Nat,
          ∀ i : Nat, cutoff ≤ i → head i ≠ value := by
      intro value
      exact Classical.byContradiction (fun hNotRare =>
        hFrequent ⟨value, by
          intro start
          exact Classical.byContradiction (fun hNoWitness =>
            hNotRare ⟨start, by
              intro i hLe hEq
              exact hNoWitness ⟨i, hLe, hEq⟩⟩)⟩)
    have hEventuallyGt :=
      eventually_gt_of_eventually_ne_each_value hRare
    intro start bound
    obtain ⟨cutoff, hCutoff⟩ := hEventuallyGt bound
    exact ⟨max start cutoff,
      Nat.le_max_left start cutoff,
      hCutoff (max start cutoff) (Nat.le_max_right start cutoff)⟩

end Pm4Lean
