import Pm4Lean.Util.List.Relation.Pairwise.Negative

namespace Pm4Lean

namespace List

theorem containsRelatedPair_of_not_pairwise_not
    {α : Type u} {R : α → α → Prop} {xs : List α}
    (hNotPairwise : ¬ List.Pairwise (fun x y => ¬ R x y) xs) :
    ContainsRelatedPair R xs := by
  classical
  induction xs with
  | nil =>
      exact False.elim (hNotPairwise List.Pairwise.nil)
  | cons x xs ih =>
      by_cases hHead : ∃ y : α, y ∈ xs ∧ R x y
      · obtain ⟨y, hYMem, hRelated⟩ := hHead
        obtain ⟨between, after, hSplit⟩ := exists_split_of_mem hYMem
        exact ⟨x, y, [], between, after, by simp [hSplit], hRelated⟩
      · have hTailNotPairwise :
            ¬ List.Pairwise (fun x y => ¬ R x y) xs := by
          intro hTailPairwise
          exact hNotPairwise
            (List.Pairwise.cons
              (fun y hYMem hRelated =>
                hHead ⟨y, hYMem, hRelated⟩)
              hTailPairwise)
        obtain ⟨first, second, before, between, after,
          hSplit, hRelated⟩ := ih hTailNotPairwise
        exact ⟨first, second, x :: before, between, after,
          by simp [hSplit], hRelated⟩

theorem containsRelatedPair_iff_not_pairwise_not
    {α : Type u} {R : α → α → Prop} {xs : List α} :
    ContainsRelatedPair R xs ↔
      ¬ List.Pairwise (fun x y => ¬ R x y) xs :=
  ⟨not_pairwise_not_of_containsRelatedPair,
    containsRelatedPair_of_not_pairwise_not⟩

end List
end Pm4Lean
