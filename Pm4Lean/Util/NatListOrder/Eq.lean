import Pm4Lean.Util.NatListOrder.Core

namespace Pm4Lean

theorem natListLe_antisymm {xs ys : List Nat}
    (hXY : NatListLe xs ys) (hYX : NatListLe ys xs) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => cases hXY
  | cons x xs ih =>
      cases ys with
      | nil => cases hXY
      | cons y ys =>
          have hHead : x = y := Nat.le_antisymm hXY.1 hYX.1
          have hTail : xs = ys := ih hXY.2 hYX.2
          simp [hHead, hTail]

theorem natListLe_iff_eq {xs ys : List Nat}
    (hXY : NatListLe xs ys) (hYX : NatListLe ys xs) :
    xs = ys :=
  natListLe_antisymm hXY hYX

end Pm4Lean
