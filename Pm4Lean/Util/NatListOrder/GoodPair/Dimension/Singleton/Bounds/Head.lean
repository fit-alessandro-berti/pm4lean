import Pm4Lean.Util.NatListOrder.GoodPair.Dimension.Singleton.Bounds.General

namespace Pm4Lean

theorem length_le_succ_head_of_singleton_cons_not_containsNatListLePair
    {x : Nat} {vectors : List (List Nat)}
    (hSingletonTail :
      ∀ xs : List Nat, xs ∈ vectors → ∃ y : Nat, xs = [y])
    (hNoPair : ¬ ContainsNatListLePair ([x] :: vectors)) :
    ([x] :: vectors).length ≤ x + 1 := by
  apply length_le_succ_of_forall_singleton_le_not_containsNatListLePair
  · intro xs hXsMem
    cases hXsMem with
    | head =>
        exact ⟨x, rfl, Nat.le_refl x⟩
    | tail _ hTailMem =>
        obtain ⟨y, hXsEq⟩ := hSingletonTail xs hTailMem
        subst hXsEq
        exact ⟨y, rfl,
          Nat.le_of_lt
            (singleton_tail_lt_of_not_containsNatListLePair_cons
              hNoPair hTailMem)⟩
  · exact hNoPair

theorem length_le_succ_head_of_length_one_cons_not_containsNatListLePair
    {x : Nat} {vectors : List (List Nat)}
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = 1)
    (hNoPair : ¬ ContainsNatListLePair ([x] :: vectors)) :
    ([x] :: vectors).length ≤ x + 1 := by
  apply length_le_succ_head_of_singleton_cons_not_containsNatListLePair
  · intro xs hXsMem
    cases xs with
    | nil =>
        cases hLength [] hXsMem
    | cons y tail =>
        cases tail with
        | nil =>
            exact ⟨y, rfl⟩
        | cons z zs =>
            cases hLength (y :: z :: zs) hXsMem
  · exact hNoPair

theorem not_length_gt_succ_head_of_length_one_cons_not_containsNatListLePair
    {x : Nat} {vectors : List (List Nat)}
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = 1)
    (hNoPair : ¬ ContainsNatListLePair ([x] :: vectors)) :
    ¬ x + 1 < ([x] :: vectors).length := by
  intro hLengthGt
  exact Nat.not_lt_of_ge
    (length_le_succ_head_of_length_one_cons_not_containsNatListLePair
      hLength hNoPair)
    hLengthGt

theorem containsNatListLePair_of_length_gt_succ_head_of_length_one_cons
    {x : Nat} {vectors : List (List Nat)}
    (hLength : ∀ xs : List Nat, xs ∈ vectors → xs.length = 1)
    (hLengthGt : x + 1 < ([x] :: vectors).length) :
    ContainsNatListLePair ([x] :: vectors) := by
  classical
  exact Classical.byContradiction (fun hNoPair =>
    not_length_gt_succ_head_of_length_one_cons_not_containsNatListLePair
      hLength hNoPair hLengthGt)

end Pm4Lean
