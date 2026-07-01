import Pm4Lean.Util.NatListOrder.GoodPair.Dimension.Singleton

namespace Pm4Lean

theorem exists_tails_not_containsNatListLePair_length_bound_of_forall_cons_head
    {vectors : List (List Nat)} {x n k : Nat}
    (hHead :
      ∀ xs : List Nat, xs ∈ vectors →
        ∃ tail : List Nat, xs = x :: tail)
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = n + 1)
    (hBound : ∀ xs : List Nat, xs ∈ vectors →
      ∀ y : Nat, y ∈ xs → y ≤ k)
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    ∃ tails : List (List Nat),
      vectors = tails.map (fun tail => x :: tail) ∧
        ¬ ContainsNatListLePair tails ∧
        (∀ tail : List Nat, tail ∈ tails → tail.length = n) ∧
        (∀ tail : List Nat, tail ∈ tails →
          ∀ y : Nat, y ∈ tail → y ≤ k) := by
  obtain ⟨tails, hEq, hNoTails, hTailsMem⟩ :=
    exists_tails_not_containsNatListLePair_of_forall_cons_head
      hHead hNoPair
  refine ⟨tails, hEq, hNoTails, ?_, ?_⟩
  · intro tail hTailMem
    have hLengthCons : (x :: tail).length = n + 1 :=
      hLength (x :: tail) (hTailsMem tail hTailMem)
    exact Nat.succ.inj (by
      simpa [Nat.add_comm] using hLengthCons)
  · intro tail hTailMem y hYMem
    exact hBound (x :: tail) (hTailsMem tail hTailMem)
      y (List.Mem.tail x hYMem)

end Pm4Lean
