namespace Pm4Lean

/-- Componentwise order on lists of natural numbers of the same shape. -/
def NatListLe : List Nat → List Nat → Prop
  | [], [] => True
  | n :: ns, m :: ms => n ≤ m ∧ NatListLe ns ms
  | _, _ => False

end Pm4Lean
