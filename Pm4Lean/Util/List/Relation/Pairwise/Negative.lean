import Pm4Lean.Util.List.Relation.Cons

namespace Pm4Lean

namespace List

theorem not_pairwise_not_of_related_pair_split
    {α : Type u} {R : α → α → Prop}
    {first second : α} {before between after : List α}
    (hRelated : R first second) :
    ¬ List.Pairwise (fun x y => ¬ R x y)
      (before ++ first :: between ++ second :: after) := by
  induction before with
  | nil =>
      intro hPairwise
      have hPairwise' :
          List.Pairwise (fun x y => ¬ R x y)
            (first :: between ++ second :: after) := by
        simpa using hPairwise
      exact (List.pairwise_cons.mp hPairwise').1 second
        (List.mem_append_right between (List.Mem.head after))
        hRelated
  | cons head before ih =>
      intro hPairwise
      have hPairwise' :
          List.Pairwise (fun x y => ¬ R x y)
            (head :: before ++ first :: between ++ second :: after) := by
        simpa using hPairwise
      exact ih (List.pairwise_cons.mp hPairwise').2

theorem not_pairwise_not_of_containsRelatedPair
    {α : Type u} {R : α → α → Prop} {xs : List α}
    (hPair : ContainsRelatedPair R xs) :
    ¬ List.Pairwise (fun x y => ¬ R x y) xs := by
  obtain ⟨first, second, before, between, after,
    hSplit, hRelated⟩ := hPair
  subst hSplit
  exact not_pairwise_not_of_related_pair_split hRelated

end List
end Pm4Lean
