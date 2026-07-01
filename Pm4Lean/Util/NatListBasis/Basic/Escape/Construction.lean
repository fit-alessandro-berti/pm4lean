import Pm4Lean.Util.NatListBasis.Basic.Definitions

namespace Pm4Lean

theorem not_containsNatListLePair_cons_of_not_dominated
    {xs : List Nat} {basis : List (List Nat)}
    (hNotDominated : ¬ NatListDominatedBy xs basis)
    (hNoPair : ¬ ContainsNatListLePair basis) :
    ¬ ContainsNatListLePair (xs :: basis) := by
  exact not_containsNatListLePair_iff_pairwise_not_natListLe.mpr
    (List.Pairwise.cons
      (fun upper hUpperMem hLe =>
        hNotDominated (natListDominatedBy_of_mem_le hUpperMem hLe))
      (not_containsNatListLePair_iff_pairwise_not_natListLe.mp hNoPair))

theorem exists_not_containsNatListLePair_list_of_forall_basis_escape
    {P : List Nat → Prop}
    (hEscape :
      ∀ basis : List (List Nat),
        ∃ xs : List Nat, P xs ∧ ¬ NatListDominatedBy xs basis)
    (n : Nat) :
    ∃ vectors : List (List Nat),
      vectors.length = n ∧
        (∀ xs : List Nat, xs ∈ vectors → P xs) ∧
        ¬ ContainsNatListLePair vectors := by
  induction n with
  | zero =>
      refine ⟨[], rfl, ?_, ?_⟩
      · intro xs hMem
        cases hMem
      · exact not_containsNatListLePair_iff_pairwise_not_natListLe.mpr
          List.Pairwise.nil
  | succ n ih =>
      obtain ⟨basis, hBasisLength, hBasisP, hNoPair⟩ := ih
      obtain ⟨xs, hP, hNotDominated⟩ := hEscape basis
      refine ⟨xs :: basis, by simp [hBasisLength], ?_, ?_⟩
      · intro ys hMem
        cases hMem with
        | head =>
            exact hP
        | tail _ hTailMem =>
            exact hBasisP ys hTailMem
      · exact not_containsNatListLePair_cons_of_not_dominated
          hNotDominated hNoPair

end Pm4Lean
