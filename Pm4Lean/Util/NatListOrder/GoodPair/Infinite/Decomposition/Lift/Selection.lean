import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Lift.Tail

namespace Pm4Lean

theorem containsNatListLePairSequence_of_indexSelection_tail
    {f tail : Nat → List Nat} {select head : Nat → Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hEq : ∀ i : Nat, f (select i) = head i :: tail i)
    (hHeadLe : ∀ i j : Nat, i < j → head i ≤ head j)
    (hTailPair : ContainsNatListLePairSequence tail) :
    ContainsNatListLePairSequence f :=
  containsNatListLePairSequence_of_indexSelection hSelect
    (containsNatListLePairSequence_of_tail hEq hHeadLe hTailPair)

theorem not_containsNatListLePairSequence_indexSelection_tail_of_not
    {f tail : Nat → List Nat} {select head : Nat → Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hEq : ∀ i : Nat, f (select i) = head i :: tail i)
    (hHeadLe : ∀ i j : Nat, i < j → head i ≤ head j)
    (hNoPair : ¬ ContainsNatListLePairSequence f) :
    ¬ ContainsNatListLePairSequence tail := by
  intro hTailPair
  exact hNoPair
    (containsNatListLePairSequence_of_indexSelection_tail
      hSelect hEq hHeadLe hTailPair)

end Pm4Lean
