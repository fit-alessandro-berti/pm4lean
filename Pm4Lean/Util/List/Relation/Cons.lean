import Pm4Lean.Util.List.Relation.Definition

namespace Pm4Lean

namespace List

theorem containsRelatedPair_cons_of_mem_related
    {α : Type u} {R : α → α → Prop} {x y : α} {xs : List α}
    (hMem : y ∈ xs) (hRelated : R x y) :
    ContainsRelatedPair R (x :: xs) := by
  obtain ⟨between, after, hSplit⟩ := exists_split_of_mem hMem
  exact ⟨x, y, [], between, after, by simp [hSplit], hRelated⟩

theorem containsRelatedPair_cons_tail
    {α : Type u} {R : α → α → Prop} {x : α} {xs : List α}
    (hPair : ContainsRelatedPair R xs) :
    ContainsRelatedPair R (x :: xs) := by
  obtain ⟨first, second, before, between, after,
    hSplit, hRelated⟩ := hPair
  exact ⟨first, second, x :: before, between, after,
    by simp [hSplit], hRelated⟩

theorem not_containsRelatedPair_tail_of_cons
    {α : Type u} {R : α → α → Prop} {x : α} {xs : List α}
    (hNoPair : ¬ ContainsRelatedPair R (x :: xs)) :
    ¬ ContainsRelatedPair R xs := by
  intro hPair
  exact hNoPair (containsRelatedPair_cons_tail hPair)

theorem not_related_head_of_not_containsRelatedPair_cons
    {α : Type u} {R : α → α → Prop} {x y : α} {xs : List α}
    (hNoPair : ¬ ContainsRelatedPair R (x :: xs))
    (hMem : y ∈ xs) :
    ¬ R x y := by
  intro hRelated
  exact hNoPair
    (containsRelatedPair_cons_of_mem_related hMem hRelated)

end List
end Pm4Lean
