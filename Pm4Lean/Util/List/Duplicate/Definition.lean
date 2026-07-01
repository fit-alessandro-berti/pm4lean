import Pm4Lean.Util.List.Duplicate.Split

namespace Pm4Lean

namespace List

def HasDuplicate {α : Type u} : List α → Prop
  | [] => False
  | x :: xs => x ∈ xs ∨ HasDuplicate xs

def ContainsDuplicatePair {α : Type u} (xs : List α) : Prop :=
  ∃ a : α, ∃ before between after : List α,
    xs = before ++ a :: between ++ a :: after

end List
end Pm4Lean
