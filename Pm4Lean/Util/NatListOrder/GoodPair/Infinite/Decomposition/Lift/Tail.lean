import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.HeadTail

namespace Pm4Lean

theorem containsNatListLePairSequence_of_tail
    {f tail : Nat → List Nat} {head : Nat → Nat}
    (hEq : ∀ i : Nat, f i = head i :: tail i)
    (hHeadLe : ∀ i j : Nat, i < j → head i ≤ head j)
    (hTailPair : ContainsNatListLePairSequence tail) :
    ContainsNatListLePairSequence f := by
  obtain ⟨i, j, hLt, hTailLe⟩ := hTailPair
  exact ⟨i, j, hLt, by
    rw [hEq i, hEq j]
    exact natListLe_cons (hHeadLe i j hLt) hTailLe⟩

theorem not_containsNatListLePairSequence_tail_of_not
    {f tail : Nat → List Nat} {head : Nat → Nat}
    (hEq : ∀ i : Nat, f i = head i :: tail i)
    (hHeadLe : ∀ i j : Nat, i < j → head i ≤ head j)
    (hNoPair : ¬ ContainsNatListLePairSequence f) :
    ¬ ContainsNatListLePairSequence tail := by
  intro hTailPair
  exact hNoPair
    (containsNatListLePairSequence_of_tail hEq hHeadLe hTailPair)

end Pm4Lean
