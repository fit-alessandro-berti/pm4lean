import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Decomposition.Lift.Selection

namespace Pm4Lean

theorem containsNatListLePairSequence_of_indexSelection_tail_const_head
    {f tail : Nat → List Nat} {select : Nat → Nat} {head : Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hEq : ∀ i : Nat, f (select i) = head :: tail i)
    (hTailPair : ContainsNatListLePairSequence tail) :
    ContainsNatListLePairSequence f :=
  containsNatListLePairSequence_of_indexSelection_tail
    hSelect hEq (fun _ _ _ => Nat.le_refl head) hTailPair

theorem not_containsNatListLePairSequence_indexSelection_tail_const_head_of_not
    {f tail : Nat → List Nat} {select : Nat → Nat} {head : Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hEq : ∀ i : Nat, f (select i) = head :: tail i)
    (hNoPair : ¬ ContainsNatListLePairSequence f) :
    ¬ ContainsNatListLePairSequence tail := by
  intro hTailPair
  exact hNoPair
    (containsNatListLePairSequence_of_indexSelection_tail_const_head
      hSelect hEq hTailPair)

end Pm4Lean
