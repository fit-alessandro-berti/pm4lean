import Pm4Lean.Util.NatListOrder.Basic

namespace Pm4Lean

/--
`NatListHasGreaterCoordinate xs ys` records an aligned coordinate where `xs`
is strictly larger than `ys`.
-/
def NatListHasGreaterCoordinate : List Nat → List Nat → Prop
  | x :: xs, y :: ys => y < x ∨ NatListHasGreaterCoordinate xs ys
  | _, _ => False

end Pm4Lean
