import Pm4Lean.Util.NatListBox.Finiteness.Bounds

namespace Pm4Lean

theorem not_nodup_of_length_gt_natListsUpTo_length
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    ¬ xss.Nodup :=
  List.not_nodup_of_length_gt_length_of_subset hLength hBounded

theorem not_nodup_of_length_gt_natListsUpTo_length_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    ¬ xss.Nodup :=
  not_nodup_of_length_gt_natListsUpTo_length hLength
    (fun xs hMem =>
      mem_natListsUpTo (hCoordLength xs hMem)
        (hCoordBound xs hMem))

theorem hasDuplicate_of_length_gt_natListsUpTo_length
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    List.HasDuplicate xss :=
  List.hasDuplicate_of_not_nodup
    (not_nodup_of_length_gt_natListsUpTo_length hLength hBounded)

theorem containsDuplicatePair_of_length_gt_natListsUpTo_length
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    List.ContainsDuplicatePair xss :=
  List.containsDuplicatePair_of_hasDuplicate
    (hasDuplicate_of_length_gt_natListsUpTo_length hLength hBounded)

theorem hasDuplicate_of_length_gt_natListsUpTo_length_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    List.HasDuplicate xss :=
  List.hasDuplicate_of_not_nodup
    (not_nodup_of_length_gt_natListsUpTo_length_of_forall
      hLength hCoordLength hCoordBound)

theorem containsDuplicatePair_of_length_gt_natListsUpTo_length_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hLength : (NatListsUpTo n k).length < xss.length)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    List.ContainsDuplicatePair xss :=
  List.containsDuplicatePair_of_hasDuplicate
    (hasDuplicate_of_length_gt_natListsUpTo_length_of_forall
      hLength hCoordLength hCoordBound)

end Pm4Lean
