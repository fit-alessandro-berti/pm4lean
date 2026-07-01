import Pm4Lean.Util.NatListBasis.Basic
import Pm4Lean.Util.NatListBox.Finiteness

namespace Pm4Lean

theorem length_le_natListsUpTo_length_of_not_containsNatListLePair_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    xss.length ≤ (NatListsUpTo bound.length (NatListMax bound)).length :=
  length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
    hNoPair
    (fun xs hMem => natListLe_length_eq (hBound xs hMem))
    (fun xs hMem => forall_le_natListMax_of_natListLe (hBound xs hMem))

theorem not_length_gt_natListsUpTo_length_of_not_containsNatListLePair_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    ¬ (NatListsUpTo bound.length (NatListMax bound)).length < xss.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_not_containsNatListLePair_of_natListLe_bound
      hNoPair hBound)
    hLength

end Pm4Lean
