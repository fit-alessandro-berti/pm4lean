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
partial-order composition.  The sequence, parallel, and `xorMany` constructors
are convenience forms that desugar to total/empty partial orders and simple
choice graphs, respectively.
-/
inductive POWL2 (Activity : Type u) where
  | tau : POWL2 Activity
  | activity : Activity → POWL2 Activity
  | ofPOWL : POWL Activity → POWL2 Activity
  | xorMany : List (POWL2 Activity) → POWL2 Activity
  | sequence : List (POWL2 Activity) → POWL2 Activity
  | parallel : List (POWL2 Activity) → POWL2 Activity
  | loop : POWL2 Activity → POWL2 Activity → POWL2 Activity
  | choiceGraph : List (POWL2 Activity) → POWL2ChoiceGraph → POWL2 Activity
  | partialOrder : List (POWL2 Activity) → (Nat → Nat → Prop) → POWL2 Activity

namespace POWL2

variable {Activity : Type u}

/-- The total order used by a POWL2 sequence block after desugaring. -/
def sequenceOrder (n : Nat) : Nat → Nat → Prop :=
  fun i j => i < j ∧ j < n

/-- The empty order used by a POWL2 parallel block after desugaring. -/
def parallelOrder : Nat → Nat → Prop :=
  fun _ _ => False

/-- The simple choice graph used by an n-ary XOR convenience node. -/
def xorChoiceGraph (n : Nat) : POWL2ChoiceGraph where
  empty := n = 0
  start := fun i => i < n
  finish := fun i => i < n
  edge := fun _ _ => False

/-- POWL2 well-formedness follows the recursive paper syntax. -/
def WellFormed : POWL2 Activity → Prop
  | tau => True
  | activity _ => True
  | ofPOWL p => POWL.WellFormed p
  | xorMany children =>
      (∀ child ∈ children, WellFormed child)
  | sequence children =>
      (∀ child ∈ children, WellFormed child)
  | parallel children =>
      (∀ child ∈ children, WellFormed child)
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
