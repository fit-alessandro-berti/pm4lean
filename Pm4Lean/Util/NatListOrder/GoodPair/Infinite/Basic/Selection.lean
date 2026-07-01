import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Basic.Prefix

namespace Pm4Lean

theorem containsNatListLePairSequence_of_indexSelection
    {f : Nat → List Nat} {select : Nat → Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hPair :
      ContainsNatListLePairSequence (fun k : Nat => f (select k))) :
    ContainsNatListLePairSequence f := by
  obtain ⟨i, j, hLt, hLe⟩ := hPair
  exact ⟨select i, select j, hSelect i j hLt, hLe⟩

theorem not_containsNatListLePairSequence_indexSelection_of_not
    {f : Nat → List Nat} {select : Nat → Nat}
    (hSelect : ∀ i j : Nat, i < j → select i < select j)
    (hNoPair : ¬ ContainsNatListLePairSequence f) :
    ¬ ContainsNatListLePairSequence (fun k : Nat => f (select k)) := by
  intro hPair
  exact hNoPair
    (containsNatListLePairSequence_of_indexSelection hSelect hPair)

theorem indexSelection_strict_of_step
    {select : Nat → Nat}
    (hStep : ∀ i : Nat, select i < select (i + 1)) :
    ∀ i j : Nat, i < j → select i < select j := by
  intro i j hLt
  have hSuccLe : i + 1 ≤ j := Nat.succ_le_of_lt hLt
  obtain ⟨d, hEq⟩ := Nat.exists_eq_add_of_le hSuccLe
  have hDistance : ∀ d : Nat, select i < select (i + 1 + d) := by
    intro d
    induction d with
    | zero =>
        simpa [Nat.add_assoc] using hStep i
    | succ d ih =>
        exact Nat.lt_trans ih (by
          simpa [Nat.add_assoc] using hStep ((i + 1) + d))
  rw [hEq]
  exact hDistance d

theorem natSequence_strict_of_step
    {a : Nat → Nat}
    (hStep : ∀ i : Nat, a i < a (i + 1)) :
    ∀ i j : Nat, i < j → a i < a j :=
  indexSelection_strict_of_step hStep

end Pm4Lean
