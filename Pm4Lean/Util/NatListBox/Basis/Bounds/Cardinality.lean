import Pm4Lean.Util.NatListBox.Basis.Bounds.Dominated
import Pm4Lean.Util.NatListBox.Finiteness

namespace Pm4Lean

theorem length_le_natListsUpTo_length_of_not_containsNatListLePair_of_basis_dominated
    {n : Nat} {basis xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll xss basis) :
    xss.length ≤ (NatListsUpTo n (NatListMax basis.flatten)).length :=
  length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
    hNoPair
    (fun xs hXsMem =>
      length_eq_of_natListDominatedBy_basis_length hBasisLength
        (hDominates xs hXsMem))
    (fun xs hXsMem =>
      forall_le_natListMax_flatten_of_natListDominatedBy
        (hDominates xs hXsMem))

theorem not_length_gt_natListsUpTo_length_of_not_containsNatListLePair_of_basis_dominated
    {n : Nat} {basis xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll xss basis) :
    ¬ (NatListsUpTo n (NatListMax basis.flatten)).length < xss.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_not_containsNatListLePair_of_basis_dominated
      hNoPair hBasisLength hDominates)
    hLength

theorem containsNatListLePair_of_length_gt_natListsUpTo_length_of_basis_dominated
    {n : Nat} {basis xss : List (List Nat)}
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hDominates : NatListBasisDominatesAll xss basis)
    (hLength :
      (NatListsUpTo n (NatListMax basis.flatten)).length < xss.length) :
    ContainsNatListLePair xss :=
  containsNatListLePair_of_length_gt_natListsUpTo_length_of_forall
    hLength
    (fun xs hXsMem =>
      length_eq_of_natListDominatedBy_basis_length hBasisLength
        (hDominates xs hXsMem))
    (fun xs hXsMem =>
      forall_le_natListMax_flatten_of_natListDominatedBy
        (hDominates xs hXsMem))

end Pm4Lean
