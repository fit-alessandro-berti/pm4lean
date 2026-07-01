import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Basic.Prefix.Range

namespace Pm4Lean

theorem exists_natListLePair_of_containsNatListLePair_map_range
    {f : Nat → List Nat} {n : Nat}
    (hPair : ContainsNatListLePair ((List.range n).map f)) :
    ∃ i j : Nat, i < j ∧ NatListLe (f i) (f j) := by
  classical
  exact Classical.byContradiction (fun hNoPair =>
    (not_containsNatListLePair_map_range_of_forall_not
      (fun i j hLt hLe => hNoPair ⟨i, j, hLt, hLe⟩))
      hPair)

theorem containsNatListLePairSequence_of_containsNatListLePair_map_range
    {f : Nat → List Nat} {n : Nat}
    (hPair : ContainsNatListLePair ((List.range n).map f)) :
    ContainsNatListLePairSequence f :=
  exists_natListLePair_of_containsNatListLePair_map_range hPair

theorem not_containsNatListLePair_map_range_of_not_sequence
    {f : Nat → List Nat} {n : Nat}
    (hNoPair : ¬ ContainsNatListLePairSequence f) :
    ¬ ContainsNatListLePair ((List.range n).map f) := by
  intro hPair
  exact hNoPair
    (containsNatListLePairSequence_of_containsNatListLePair_map_range hPair)

end Pm4Lean
