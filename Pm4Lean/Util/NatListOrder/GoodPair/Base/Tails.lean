import Pm4Lean.Util.NatListOrder.GoodPair.Base.Pairwise

namespace Pm4Lean

theorem exists_tails_of_forall_cons_head
    {x : Nat} {vectors : List (List Nat)}
    (hHead :
      ∀ xs : List Nat, xs ∈ vectors →
        ∃ tail : List Nat, xs = x :: tail) :
    ∃ tails : List (List Nat),
      vectors = tails.map (fun tail => x :: tail) ∧
        ∀ tail : List Nat, tail ∈ tails → x :: tail ∈ vectors := by
  induction vectors with
  | nil =>
      exact ⟨[], rfl, by
        intro tail hMem
        cases hMem⟩
  | cons head tail ih =>
      obtain ⟨headTail, hHeadEq⟩ :=
        hHead head (List.Mem.head tail)
      subst hHeadEq
      have hTailHead :
          ∀ xs : List Nat, xs ∈ tail →
            ∃ tail' : List Nat, xs = x :: tail' := by
        intro xs hXsMem
        exact hHead xs (List.Mem.tail (x :: headTail) hXsMem)
      obtain ⟨tails, hTailEq, hTailsMem⟩ := ih hTailHead
      exact ⟨headTail :: tails, by simp [hTailEq], by
        intro tail' hTailMem
        cases hTailMem with
        | head =>
            exact List.Mem.head tail
        | tail _ hMem =>
            exact List.Mem.tail (x :: headTail)
              (hTailsMem tail' hMem)⟩

theorem exists_tails_not_containsNatListLePair_of_forall_cons_head
    {x : Nat} {vectors : List (List Nat)}
    (hHead :
      ∀ xs : List Nat, xs ∈ vectors →
        ∃ tail : List Nat, xs = x :: tail)
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    ∃ tails : List (List Nat),
      vectors = tails.map (fun tail => x :: tail) ∧
        ¬ ContainsNatListLePair tails ∧
        ∀ tail : List Nat, tail ∈ tails → x :: tail ∈ vectors := by
  obtain ⟨tails, hEq, hTailsMem⟩ :=
    exists_tails_of_forall_cons_head hHead
  have hNoTails : ¬ ContainsNatListLePair tails := by
    intro hPair
    exact hNoPair (by
      rw [hEq]
      exact containsNatListLePair_map_cons_of_containsNatListLePair hPair)
  exact ⟨tails, hEq, hNoTails, hTailsMem⟩

end Pm4Lean
