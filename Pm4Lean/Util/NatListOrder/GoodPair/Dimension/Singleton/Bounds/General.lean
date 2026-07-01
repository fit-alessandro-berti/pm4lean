import Pm4Lean.Util.NatListOrder.GoodPair.Dimension.Singleton.Nodup

namespace Pm4Lean

theorem length_le_succ_of_forall_singleton_le_not_containsNatListLePair
    {vectors : List (List Nat)} {k : Nat}
    (hSingletonBound :
      ∀ xs : List Nat, xs ∈ vectors →
        ∃ x : Nat, xs = [x] ∧ x ≤ k)
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    vectors.length ≤ k + 1 := by
  have hSingleton :
      ∀ xs : List Nat, xs ∈ vectors → ∃ x : Nat, xs = [x] := by
    intro xs hXsMem
    obtain ⟨x, hEq, _hBound⟩ := hSingletonBound xs hXsMem
    exact ⟨x, hEq⟩
  have hNodup : vectors.Nodup :=
    nodup_of_forall_singleton_not_containsNatListLePair
      hSingleton hNoPair
  have hSubset :
      ∀ xs : List Nat, xs ∈ vectors →
        xs ∈ (List.range (k + 1)).map (fun x : Nat => [x]) := by
    intro xs hXsMem
    obtain ⟨x, hEq, hBound⟩ := hSingletonBound xs hXsMem
    subst hEq
    exact List.mem_map.mpr
      ⟨x, by
        rw [List.mem_range]
        exact Nat.lt_succ_of_le hBound,
        rfl⟩
  have hLength :=
    List.length_le_length_of_nodup_subset hNodup hSubset
  simpa [List.length_map] using hLength

theorem length_le_succ_of_forall_length_one_bounded_not_containsNatListLePair
    {vectors : List (List Nat)} {k : Nat}
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = 1)
    (hBound : ∀ xs : List Nat, xs ∈ vectors →
      ∀ x : Nat, x ∈ xs → x ≤ k)
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    vectors.length ≤ k + 1 := by
  apply length_le_succ_of_forall_singleton_le_not_containsNatListLePair
  · intro xs hXsMem
    cases xs with
    | nil =>
        cases hLength [] hXsMem
    | cons x tail =>
        cases tail with
        | nil =>
            exact ⟨x, rfl,
              hBound [x] hXsMem x (List.Mem.head [])⟩
        | cons y ys =>
            cases hLength (x :: y :: ys) hXsMem
  · exact hNoPair

end Pm4Lean
