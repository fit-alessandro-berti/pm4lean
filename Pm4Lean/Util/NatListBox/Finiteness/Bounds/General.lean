import Pm4Lean.Util.List.Finiteness
import Pm4Lean.Util.NatListBox.Basic

namespace Pm4Lean

theorem length_le_natListsUpTo_length_of_nodup
    {n k : Nat} {xss : List (List Nat)}
    (hNodup : xss.Nodup)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    xss.length ≤ (NatListsUpTo n k).length :=
  List.length_le_length_of_nodup_subset hNodup hBounded

theorem length_le_natListsUpTo_length_of_not_containsNatListLePair
    {n k : Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    xss.length ≤ (NatListsUpTo n k).length :=
  length_le_natListsUpTo_length_of_nodup
    (nodup_of_not_containsNatListLePair hNoPair)
    hBounded

theorem length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    xss.length ≤ (NatListsUpTo n k).length :=
  length_le_natListsUpTo_length_of_not_containsNatListLePair hNoPair
    (fun xs hMem =>
      mem_natListsUpTo (hCoordLength xs hMem)
        (hCoordBound xs hMem))

theorem not_length_gt_natListsUpTo_length_of_not_containsNatListLePair
    {n k : Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hBounded :
      ∀ xs : List Nat, xs ∈ xss → xs ∈ NatListsUpTo n k) :
    ¬ (NatListsUpTo n k).length < xss.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_not_containsNatListLePair
      hNoPair hBounded)
    hLength

theorem not_length_gt_natListsUpTo_length_of_not_containsNatListLePair_of_forall
    {n k : Nat} {xss : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair xss)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k) :
    ¬ (NatListsUpTo n k).length < xss.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
      hNoPair hCoordLength hCoordBound)
    hLength

end Pm4Lean
