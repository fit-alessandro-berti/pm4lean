import Pm4Lean.Util.NatListBasis.Coverage

namespace Pm4Lean

theorem natListMax_le_natListMax_flatten_of_mem
    {basis : List (List Nat)} {upper : List Nat}
    (hUpperMem : upper ∈ basis) :
    NatListMax upper ≤ NatListMax basis.flatten :=
  natListMax_le_of_forall (fun _ hXMem =>
    le_natListMax_of_mem
      (List.mem_flatten.mpr ⟨upper, hUpperMem, hXMem⟩))

theorem forall_le_natListMax_flatten_of_natListDominatedBy
    {basis : List (List Nat)} {xs : List Nat}
    (hDominated : NatListDominatedBy xs basis) :
    ∀ x : Nat, x ∈ xs → x ≤ NatListMax basis.flatten := by
  obtain ⟨upper, hUpperMem, hLe⟩ := hDominated
  intro x hXMem
  exact Nat.le_trans
    (forall_le_natListMax_of_natListLe hLe x hXMem)
    (natListMax_le_natListMax_flatten_of_mem hUpperMem)

theorem length_eq_of_natListDominatedBy_basis_length
    {basis : List (List Nat)} {xs : List Nat} {n : Nat}
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominated : NatListDominatedBy xs basis) :
    xs.length = n := by
  obtain ⟨upper, hUpperMem, hLe⟩ := hDominated
  rw [natListLe_length_eq hLe, hBasisLength upper hUpperMem]

end Pm4Lean
