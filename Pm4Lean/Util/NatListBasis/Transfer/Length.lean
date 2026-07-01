import Pm4Lean.Util.NatListBasis.Transfer.Trans

namespace Pm4Lean

theorem natListDominatedBy_filter_length_eq
    {xs : List Nat} {basis : List (List Nat)} {n : Nat}
    (hLength : xs.length = n)
    (hDominated : NatListDominatedBy xs basis) :
    NatListDominatedBy xs
      (basis.filter (fun upper => upper.length = n)) := by
  obtain ⟨upper, hMem, hLe⟩ := hDominated
  refine ⟨upper, ?_, hLe⟩
  apply List.mem_filter.mpr
  constructor
  · exact hMem
  · have hUpperLength : upper.length = n := by
      rw [← natListLe_length_eq hLe]
      exact hLength
    simp [hUpperLength]

theorem natListBasisDominatesAll_filter_length_eq
    {vectors basis : List (List Nat)} {n : Nat}
    (hLength :
      ∀ xs : List Nat, xs ∈ vectors → xs.length = n)
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll vectors
      (basis.filter (fun upper => upper.length = n)) := by
  intro xs hMem
  exact natListDominatedBy_filter_length_eq
    (hLength xs hMem)
    (hDominates xs hMem)

end Pm4Lean
