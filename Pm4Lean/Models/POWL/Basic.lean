namespace Pm4Lean
namespace ProcessModel

/-- Atomic and composite POWL terms. -/
inductive POWL (Activity : Type u) where
  | tau : POWL Activity
  | activity : Activity → POWL Activity
  | xor : POWL Activity → POWL Activity → POWL Activity
  | loop : POWL Activity → POWL Activity → POWL Activity
  | partialOrder : List (POWL Activity) → (Nat → Nat → Prop) → POWL Activity

namespace POWL

variable {Activity : Type u}

/-- A binary relation is irreflexive on a finite index range. -/
def IrreflexiveOnRange (n : Nat) (r : Nat → Nat → Prop) : Prop :=
  ∀ i, i < n → ¬ r i i

/-- A binary relation is transitive on a finite index range. -/
def TransitiveOnRange (n : Nat) (r : Nat → Nat → Prop) : Prop :=
  ∀ i j k, i < n → j < n → k < n → r i j → r j k → r i k

/-- Well-formedness for POWL partial-order nodes. -/
def WellFormed : POWL Activity → Prop
  | tau => True
  | activity _ => True
  | xor l r => WellFormed l ∧ WellFormed r
  | loop body redo => WellFormed body ∧ WellFormed redo
  | partialOrder children order =>
      (∀ child ∈ children, WellFormed child) ∧
      IrreflexiveOnRange children.length order ∧
      TransitiveOnRange children.length order

end POWL
end ProcessModel
end Pm4Lean
