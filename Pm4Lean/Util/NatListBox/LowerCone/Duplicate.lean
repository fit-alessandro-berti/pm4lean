import Pm4Lean.Util.NatListBox.LowerCone.Bounds

namespace Pm4Lean

theorem not_nodup_of_length_gt_natListsUpTo_length_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    ¬ xss.Nodup :=
  not_nodup_of_length_gt_natListsUpTo_length_of_forall hLength
    (fun xs hMem => natListLe_length_eq (hBound xs hMem))
    (fun xs hMem => forall_le_natListMax_of_natListLe (hBound xs hMem))

theorem hasDuplicate_of_length_gt_natListsUpTo_length_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    List.HasDuplicate xss :=
  List.hasDuplicate_of_not_nodup
    (not_nodup_of_length_gt_natListsUpTo_length_of_natListLe_bound
      hLength hBound)

theorem containsDuplicatePair_of_length_gt_natListsUpTo_length_of_natListLe_bound
    {bound : List Nat} {xss : List (List Nat)}
    (hLength :
      (NatListsUpTo bound.length (NatListMax bound)).length < xss.length)
    (hBound : ∀ xs : List Nat, xs ∈ xss → NatListLe xs bound) :
    List.ContainsDuplicatePair xss :=
  List.containsDuplicatePair_of_hasDuplicate
    (hasDuplicate_of_length_gt_natListsUpTo_length_of_natListLe_bound
      hLength hBound)

end Pm4Lean
