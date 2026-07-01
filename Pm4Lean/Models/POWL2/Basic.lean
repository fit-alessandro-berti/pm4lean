import Pm4Lean.Models.POWL.Basic

namespace Pm4Lean
namespace ProcessModel

/-- The edge relation of a POWL 2.0 choice graph over child-model indices. -/
structure POWL2ChoiceGraph where
  empty : Prop
  start : Nat → Prop
  finish : Nat → Prop
  edge : Nat → Nat → Prop

namespace POWL2ChoiceGraph

/-- All choice-graph references stay within the finite child-index range. -/
def WellFormed (childCount : Nat) (g : POWL2ChoiceGraph) : Prop :=
  (∀ i, g.start i → i < childCount) ∧
  (∀ i, g.finish i → i < childCount) ∧
  (∀ i j, g.edge i j → i < childCount ∧ j < childCount)

end POWL2ChoiceGraph

/--
POWL 2.0 syntax.

POWL 2.0 replaces POWL's n-ary XOR with choice graphs while keeping loop and
partial-order composition.
-/
inductive POWL2 (Activity : Type u) where
  | tau : POWL2 Activity
  | activity : Activity → POWL2 Activity
  | loop : POWL2 Activity → POWL2 Activity → POWL2 Activity
  | choiceGraph : List (POWL2 Activity) → POWL2ChoiceGraph → POWL2 Activity
  | partialOrder : List (POWL2 Activity) → (Nat → Nat → Prop) → POWL2 Activity

namespace POWL2

variable {Activity : Type u}

/-- POWL2 well-formedness follows the recursive paper syntax. -/
def WellFormed : POWL2 Activity → Prop
  | tau => True
  | activity _ => True
  | loop body redo => WellFormed body ∧ WellFormed redo
  | choiceGraph children graph =>
      (∀ child ∈ children, WellFormed child) ∧
      POWL2ChoiceGraph.WellFormed children.length graph
  | partialOrder children order =>
      (∀ child ∈ children, WellFormed child) ∧
      POWL.IrreflexiveOnRange children.length order ∧
      POWL.TransitiveOnRange children.length order

end POWL2
end ProcessModel
end Pm4Lean
