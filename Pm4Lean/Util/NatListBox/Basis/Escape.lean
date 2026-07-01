import Pm4Lean.Util.NatListBox.Basis.Bounds

namespace Pm4Lean

theorem exists_not_natListDominatedBy_of_not_containsNatListLePair_length_gt_basis
    {n : Nat} {basis xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧ ¬ NatListDominatedBy xs basis := by
  classical
  exact Classical.byContradiction (fun hNoWitness =>
    let hDominates : NatListBasisDominatesAll xss basis := by
      intro xs hXsMem
      by_cases hDominated : NatListDominatedBy xs basis
      · exact hDominated
      · exact False.elim (hNoWitness ⟨xs, hXsMem, hDominated⟩)
    not_length_gt_natListsUpTo_length_of_not_containsNatListLePair_of_basis_dominated
      hNoPair hBasisLength hDominates hLength)

theorem exists_basisGreaterCoordinateWitness_of_not_containsNatListLePair_length_gt_basis
    {n : Nat} {basis xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧
      NatListBasisHasGreaterCoordinateWitness xs basis := by
  obtain ⟨xs, hXsMem, hNotDominated⟩ :=
    exists_not_natListDominatedBy_of_not_containsNatListLePair_length_gt_basis
      hNoPair hBasisLength hLength
  exact ⟨xs, hXsMem,
    natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
      (hCoordLength xs hXsMem) hBasisLength hNotDominated⟩

end Pm4Lean
