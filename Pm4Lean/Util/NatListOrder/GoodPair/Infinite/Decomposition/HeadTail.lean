import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Head

namespace Pm4Lean

theorem exists_cons_of_length_eq_succ
    {xs : List Nat} {n : Nat}
    (hLength : xs.length = n + 1) :
    ∃ x : Nat, ∃ tail : List Nat,
      xs = x :: tail ∧ tail.length = n := by
  cases xs with
  | nil =>
      cases hLength
  | cons x tail =>
      exact ⟨x, tail, rfl, Nat.succ.inj (by
        simpa [Nat.add_comm] using hLength)⟩

theorem exists_head_tail_sequence_of_forall_length_succ
    {f : Nat → List Nat} {n : Nat}
    (hLength : ∀ i : Nat, (f i).length = n + 1) :
    ∃ head : Nat → Nat,
      ∃ tail : Nat → List Nat,
        (∀ i : Nat, f i = head i :: tail i) ∧
          (∀ i : Nat, (tail i).length = n) := by
  classical
  have hExists :
      ∀ i : Nat, ∃ ht : Nat × List Nat,
        f i = ht.1 :: ht.2 ∧ ht.2.length = n := by
    intro i
    obtain ⟨x, tail, hEq, hTailLength⟩ :=
      exists_cons_of_length_eq_succ (hLength i)
    exact ⟨(x, tail), hEq, hTailLength⟩
  refine ⟨fun i => (Classical.choose (hExists i)).1,
    fun i => (Classical.choose (hExists i)).2, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (hExists i)).1
  · intro i
    exact (Classical.choose_spec (hExists i)).2

end Pm4Lean
