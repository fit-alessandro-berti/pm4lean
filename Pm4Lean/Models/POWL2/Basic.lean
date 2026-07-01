import Pm4Lean.Models.POWL.Basic

namespace Pm4Lean
namespace ProcessModel

/--
POWL 2.0 syntax.

The `ofPOWL` constructor embeds all existing POWL terms.  The remaining
constructors add n-ary choice, sequence, and parallel blocks while keeping the
explicit partial-order node available.
-/
inductive POWL2 (Activity : Type u) where
  | ofPOWL : POWL Activity → POWL2 Activity
  | xorMany : List (POWL2 Activity) → POWL2 Activity
  | sequence : List (POWL2 Activity) → POWL2 Activity
  | parallel : List (POWL2 Activity) → POWL2 Activity
  | loop : POWL2 Activity → POWL2 Activity → POWL2 Activity
  | partialOrder : List (POWL2 Activity) → (Nat → Nat → Prop) → POWL2 Activity

namespace POWL2

variable {Activity : Type u}

/-- Fold an n-ary exclusive choice back into the original binary POWL syntax. -/
def foldXor : List (POWL Activity) → POWL Activity
  | [] => POWL.tau
  | [p] => p
  | p :: ps => POWL.xor p (foldXor ps)

/-- The total order used by a POWL2 sequence block after desugaring. -/
def sequenceOrder (n : Nat) : Nat → Nat → Prop :=
  fun i j => i < j ∧ j < n

/-- The empty order used by a POWL2 parallel block after desugaring. -/
def parallelOrder : Nat → Nat → Prop :=
  fun _ _ => False

/-- Desugar POWL2 to the original POWL core. -/
def toPOWL : POWL2 Activity → POWL Activity
  | ofPOWL p => p
  | xorMany children => foldXor (children.map toPOWL)
  | sequence children =>
      POWL.partialOrder (children.map toPOWL)
        (sequenceOrder children.length)
  | parallel children =>
      POWL.partialOrder (children.map toPOWL) parallelOrder
  | loop body redo => POWL.loop (toPOWL body) (toPOWL redo)
  | partialOrder children order =>
      POWL.partialOrder (children.map toPOWL) order

/-- POWL2 well-formedness is inherited from the desugared POWL core. -/
def WellFormed (p : POWL2 Activity) : Prop :=
  POWL.WellFormed (toPOWL p)

end POWL2
end ProcessModel
end Pm4Lean
