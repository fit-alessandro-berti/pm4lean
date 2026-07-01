import Pm4Lean.Util.List.Duplicate

namespace Pm4Lean

namespace List

def ContainsRelatedPair {α : Type u} (R : α → α → Prop)
    (xs : List α) : Prop :=
  ∃ first second : α,
    ∃ before between after : List α,
      xs = before ++ first :: between ++ second :: after ∧
        R first second

end List
end Pm4Lean
