import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.BaseCases

namespace Pm4Lean

theorem exists_natListLePair_of_forall_length_sequence
    (n : Nat) (f : Nat → List Nat)
    (hLength : ∀ i : Nat, (f i).length = n) :
    ContainsNatListLePairSequence f := by
  induction n generalizing f with
  | zero =>
      exact exists_natListLePair_of_forall_length_zero_sequence f hLength
  | succ n ih =>
      obtain ⟨headSeq, tailSeq, hEq, hTailLength⟩ :=
        exists_head_tail_sequence_of_forall_length_succ
          (n := n) hLength
      obtain hConst | hOrdered :=
        exists_indexSelection_const_or_ordered_head_tail
          (f := f) (headSeq := headSeq) (tailSeq := tailSeq) hEq
      · obtain ⟨value, select, selectedTail, hSelect, hSelectedEq,
          hSelectedTailEq⟩ := hConst
        have hSelectedTailLength :
            ∀ i : Nat, (selectedTail i).length = n := by
          intro i
          rw [hSelectedTailEq i]
          exact hTailLength (select i)
        exact
          containsNatListLePairSequence_of_indexSelection_tail_const_head
            hSelect hSelectedEq (ih selectedTail hSelectedTailLength)
      · obtain ⟨select, selectedHead, selectedTail, hSelect,
          hSelectedEq, hSelectedHeadLe, _hSelectedHeadEq,
          hSelectedTailEq⟩ := hOrdered
        have hSelectedTailLength :
            ∀ i : Nat, (selectedTail i).length = n := by
          intro i
          rw [hSelectedTailEq i]
          exact hTailLength (select i)
        exact
          containsNatListLePairSequence_of_indexSelection_tail
            hSelect hSelectedEq hSelectedHeadLe
            (ih selectedTail hSelectedTailLength)

theorem exists_containsNatListLePair_map_range_of_forall_length_sequence
    (n : Nat) (f : Nat → List Nat)
    (hLength : ∀ i : Nat, (f i).length = n) :
    ∃ prefixLength : Nat,
      ContainsNatListLePair ((List.range prefixLength).map f) :=
  exists_containsNatListLePair_map_range_of_sequence
    (exists_natListLePair_of_forall_length_sequence n f hLength)

end Pm4Lean
