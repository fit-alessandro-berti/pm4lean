import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition

namespace Pm4Lean

theorem exists_natListLePair_of_forall_length_zero_sequence
    (f : Nat → List Nat)
    (hLength : ∀ i : Nat, (f i).length = 0) :
    ∃ i j : Nat, i < j ∧ NatListLe (f i) (f j) := by
  have hF0 : f 0 = [] :=
    List.eq_nil_of_length_eq_zero (hLength 0)
  have hF1 : f 1 = [] :=
    List.eq_nil_of_length_eq_zero (hLength 1)
  exact ⟨0, 1, Nat.zero_lt_one, by
    rw [hF0, hF1]
    trivial⟩

end Pm4Lean
