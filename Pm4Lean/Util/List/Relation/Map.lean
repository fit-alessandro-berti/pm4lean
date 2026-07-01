import Pm4Lean.Util.List.Relation.Definition

namespace Pm4Lean

namespace List

theorem containsRelatedPair_map
    {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : β → β → Prop}
    {f : α → β} {xs : List α}
    (hPair : ContainsRelatedPair R xs)
    (hRelated : ∀ {x y : α}, R x y → S (f x) (f y)) :
    ContainsRelatedPair S (xs.map f) := by
  obtain ⟨first, second, before, between, after,
    hSplit, hRel⟩ := hPair
  subst hSplit
  exact ⟨f first, f second, before.map f, between.map f, after.map f,
    by simp [List.map_append], hRelated hRel⟩

end List
end Pm4Lean
