import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.BaseCases.Zero

namespace Pm4Lean

theorem exists_natListLePair_of_forall_length_one_sequence
    (f : Nat → List Nat)
    (hLength : ∀ i : Nat, (f i).length = 1) :
    ∃ i j : Nat, i < j ∧ NatListLe (f i) (f j) := by
  classical
  exact Classical.byContradiction (fun hNoPair =>
    have hNoLe :
        ∀ i j : Nat, i < j → ¬ NatListLe (f i) (f j) := by
      intro i j hLt hLe
      exact hNoPair ⟨i, j, hLt, hLe⟩
    have hF0 : ∃ x : Nat, f 0 = [x] := by
      cases hEq : f 0 with
      | nil =>
          have hLen := hLength 0
          rw [hEq] at hLen
          cases hLen
      | cons x tail =>
          cases tail with
          | nil =>
              exact ⟨x, rfl⟩
          | cons y ys =>
              have hLen := hLength 0
              rw [hEq] at hLen
              cases hLen
    let x := hF0.choose
    let tail := (List.range (x + 1)).map (fun i => f (i + 1))
    have hF0Eq : f 0 = [x] := hF0.choose_spec
    have hTailLength :
        ∀ xs : List Nat, xs ∈ tail → xs.length = 1 := by
      intro xs hXsMem
      obtain ⟨i, _hIMem, hEq⟩ := List.mem_map.mp hXsMem
      rw [← hEq]
      exact hLength (i + 1)
    have hPrefixEq :
        (List.range (x + 2)).map f = [x] :: tail := by
      have hTwo : x + 2 = (x + 1) + 1 := by
        simp
      have hRange :
          List.range (x + 2) =
            0 :: (List.range (x + 1)).map Nat.succ := by
        rw [hTwo]
        simpa
          using List.range_succ_eq_map (n := x + 1)
      rw [hRange]
      simp [tail, hF0Eq, Nat.succ_eq_add_one]
    have hNoPrefix : ¬ ContainsNatListLePair ([x] :: tail) := by
      rw [← hPrefixEq]
      exact not_containsNatListLePair_map_range_of_forall_not hNoLe
    have hLengthGt : x + 1 < ([x] :: tail).length := by
      simp [tail]
    not_length_gt_succ_head_of_length_one_cons_not_containsNatListLePair
      hTailLength hNoPrefix hLengthGt)

end Pm4Lean
