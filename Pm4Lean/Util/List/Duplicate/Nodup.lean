import Pm4Lean.Util.List.Duplicate.Definition

namespace Pm4Lean

namespace List

theorem not_nodup_of_duplicate_split
    {α : Type u} {a : α}
    {before between after : List α} :
    ¬ (before ++ a :: between ++ a :: after).Nodup := by
  induction before with
  | nil =>
      intro hNodup
      have hNotMem := (List.nodup_cons.mp hNodup).1
      exact hNotMem
        (List.mem_append_right between (List.Mem.head after))
  | cons b before ih =>
      intro hNodup
      exact ih (List.nodup_cons.mp hNodup).2

theorem not_nodup_of_containsDuplicatePair
    {α : Type u} {xs : List α}
    (hPair : ContainsDuplicatePair xs) :
    ¬ xs.Nodup := by
  obtain ⟨a, before, between, after, hSplit⟩ := hPair
  subst hSplit
  exact not_nodup_of_duplicate_split

end List
end Pm4Lean
