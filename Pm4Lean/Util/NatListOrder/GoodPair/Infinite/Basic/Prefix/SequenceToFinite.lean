import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Basic.Prefix.FiniteToSequence

namespace Pm4Lean

theorem containsNatListLePair_map_range_of_sequence_pair
    {f : Nat → List Nat} {i j n : Nat}
    (hI : i < n) (hJ : j < n)
    (hLt : i < j) (hLe : NatListLe (f i) (f j)) :
    ContainsNatListLePair ((List.range n).map f) := by
  rw [containsNatListLePair_iff_not_pairwise_not_natListLe]
  intro hPairwise
  have hLen : ((List.range n).map f).length = n := by
    simp
  have hIMap : ((List.range n).map f)[i]'(by simpa [hLen] using hI) = f i := by
    simp [List.getElem_map, List.getElem_range]
  have hJMap : ((List.range n).map f)[j]'(by simpa [hLen] using hJ) = f j := by
    simp [List.getElem_map, List.getElem_range]
  have hNotLe :=
    (List.pairwise_iff_getElem.mp hPairwise)
      i j
      (by simpa [hLen] using hI)
      (by simpa [hLen] using hJ)
      hLt
  rw [hIMap, hJMap] at hNotLe
  exact hNotLe hLe

theorem exists_containsNatListLePair_map_range_of_sequence
    {f : Nat → List Nat}
    (hPair : ContainsNatListLePairSequence f) :
    ∃ n : Nat, ContainsNatListLePair ((List.range n).map f) := by
  obtain ⟨i, j, hLt, hLe⟩ := hPair
  exact ⟨j + 1,
    containsNatListLePair_map_range_of_sequence_pair
      (Nat.lt_trans hLt (Nat.lt_succ_self j))
      (Nat.lt_succ_self j)
      hLt hLe⟩

end Pm4Lean
