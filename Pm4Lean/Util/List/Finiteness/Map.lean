namespace Pm4Lean

namespace List

theorem nodup_map_of_injective
    {α : Type u} {β : Type v} {f : α → β} {xs : List α}
    (hInjective : Function.Injective f)
    (hNodup : xs.Nodup) :
    (xs.map f).Nodup :=
  List.Pairwise.map f
    (fun _ _ hNe hEq => hNe (hInjective hEq))
    hNodup

end List
end Pm4Lean
