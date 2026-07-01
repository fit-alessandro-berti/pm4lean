import Pm4Lean.Util.NatListBox.Finiteness.Duplicate

namespace Pm4Lean

theorem containsNatListLePair_of_length_gt_natListsUpTo_length
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    ContainsNatListLePair xss :=
  containsNatListLePair_of_containsDuplicatePair
    (containsDuplicatePair_of_length_gt_natListsUpTo_length
      hLength hBounded)

theorem containsNatListLePair_of_length_gt_natListsUpTo_length_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    ContainsNatListLePair xss :=
  containsNatListLePair_of_containsDuplicatePair
    (containsDuplicatePair_of_length_gt_natListsUpTo_length_of_forall
      hLength hCoordLength hCoordBound)

end Pm4Lean
