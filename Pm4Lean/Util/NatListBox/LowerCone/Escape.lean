import Pm4Lean.Util.NatListBox.LowerCone.Bounds

namespace Pm4Lean

theorem exists_not_natListLe_of_not_containsNatListLePair_length_gt_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧ ¬ NatListLe xs bound := by
  classical
  exact Classical.byContradiction (fun hNoWitness =>
    let hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound := by
      intro xs hXsMem
      by_cases hLe : NatListLe xs bound
      · exact hLe
      · exact False.elim (hNoWitness ⟨xs, hXsMem, hLe⟩)
    not_length_gt_natListsUpTo_length_of_not_containsNatListLePair_of_natListLe_bound
      hNoPair hBound hLength)

theorem exists_not_natListDominatedBy_singleton_of_not_containsNatListLePair_length_gt_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧ ¬ NatListDominatedBy xs [bound] := by
  obtain ⟨xs, hXsMem, hNotLe⟩ :=
    exists_not_natListLe_of_not_containsNatListLePair_length_gt_natListLe_bound
      hNoPair hLength
  exact ⟨xs, hXsMem, not_natListDominatedBy_singleton_iff.mpr hNotLe⟩

theorem exists_natListHasGreaterCoordinate_of_not_containsNatListLePair_length_gt_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = bound.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧
      NatListHasGreaterCoordinate xs bound := by
  obtain ⟨xs, hXsMem, hNotLe⟩ :=
    exists_not_natListLe_of_not_containsNatListLePair_length_gt_natListLe_bound
      hNoPair hLength
  exact ⟨xs, hXsMem,
    natListHasGreaterCoordinate_of_not_natListLe
      (hCoordLength xs hXsMem) hNotLe⟩

theorem exists_basisGreaterCoordinateWitness_singleton_of_not_containsNatListLePair_length_gt_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = bound.length)
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length) :
    ∃ xs : List Nat, xs ∈ xss ∧
      NatListBasisHasGreaterCoordinateWitness xs [bound] := by
  obtain ⟨xs, hXsMem, hGreater⟩ :=
    exists_natListHasGreaterCoordinate_of_not_containsNatListLePair_length_gt_natListLe_bound
      hNoPair hCoordLength hLength
  exact ⟨xs, hXsMem,
    natListBasisHasGreaterCoordinateWitness_singleton_iff.mpr hGreater⟩

end Pm4Lean
