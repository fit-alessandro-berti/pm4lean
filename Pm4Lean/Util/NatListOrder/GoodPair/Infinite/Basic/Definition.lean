import Pm4Lean.Util.NatListOrder.GoodPair.Dimension

namespace Pm4Lean

def ContainsNatListLePairSequence (f : Nat → List Nat) : Prop :=
  ∃ i j : Nat, i < j ∧ NatListLe (f i) (f j)

end Pm4Lean
