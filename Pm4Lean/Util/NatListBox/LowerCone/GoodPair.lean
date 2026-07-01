import Pm4Lean.Util.NatListBox.LowerCone.Duplicate

namespace Pm4Lean

theorem containsNatListLePair_of_length_gt_natListsUpTo_length_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    ContainsNatListLePair xss :=
  containsNatListLePair_of_containsDuplicatePair
    (containsDuplicatePair_of_length_gt_natListsUpTo_length_of_natListLe_bound
      hLength hBound)

end Pm4Lean
