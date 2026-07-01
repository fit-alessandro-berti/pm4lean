import Pm4Lean.Util.NatListBox.Finiteness.Bounds.General

namespace Pm4Lean

theorem length_le_natListsUpTo_length_of_forall_cons_head_not_containsNatListLePair
    {n k head : Nat} {xss : List (List Nat)}
    (hHead :
      ∀ xs : List Nat, xs ∈ xss →
        ∃ tail : List Nat, xs = head :: tail)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n + 1)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k)
    (hNoPair : ¬ ContainsNatListLePair xss) :
    xss.length ≤ (NatListsUpTo n k).length := by
  obtain ⟨tails, hEq, hNoTailPair, hTailLength, hTailBound⟩ :=
    exists_tails_not_containsNatListLePair_length_bound_of_forall_cons_head
      hHead hCoordLength hCoordBound hNoPair
  have hTailLengthLe :
      tails.length ≤ (NatListsUpTo n k).length :=
    length_le_natListsUpTo_length_of_not_containsNatListLePair_of_forall
      hNoTailPair hTailLength hTailBound
  simpa [hEq, List.length_map] using hTailLengthLe

theorem not_length_gt_natListsUpTo_length_of_forall_cons_head_not_containsNatListLePair
    {n k head : Nat} {xss : List (List Nat)}
    (hHead :
      ∀ xs : List Nat, xs ∈ xss →
        ∃ tail : List Nat, xs = head :: tail)
    (hCoordLength : ∀ xs : List Nat, xs ∈ xss → xs.length = n + 1)
    (hCoordBound :
      ∀ xs : List Nat, xs ∈ xss → ∀ x : Nat, x ∈ xs → x ≤ k)
    (hNoPair : ¬ ContainsNatListLePair xss) :
    ¬ (NatListsUpTo n k).length < xss.length := by
  intro hLength
  exact Nat.not_lt_of_ge
    (length_le_natListsUpTo_length_of_forall_cons_head_not_containsNatListLePair
      hHead hCoordLength hCoordBound hNoPair)
    hLength

end Pm4Lean
