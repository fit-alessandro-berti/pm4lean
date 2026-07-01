import Pm4Lean.Util.NatListOrder.GoodPair.Dimension.Zero

namespace Pm4Lean

theorem singleton_tail_lt_of_not_containsNatListLePair_cons
    {x y : Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair ([x] :: vectors))
    (hMem : [y] ∈ vectors) :
    y < x := by
  have hNotLe : ¬ x ≤ y := by
    intro hLe
    exact not_natListLe_head_of_not_containsNatListLePair_cons
      hNoPair hMem
      (natListLe_singleton_iff.mpr hLe)
  exact Nat.lt_of_not_ge hNotLe

end Pm4Lean
