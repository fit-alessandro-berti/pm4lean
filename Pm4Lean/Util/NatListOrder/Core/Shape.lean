import Pm4Lean.Util.NatListOrder.Core.Cons

namespace Pm4Lean

theorem natListLe_length_eq {xs ys : List Nat}
    (hLe : NatListLe xs ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => cases hLe
  | cons x xs ih =>
      cases ys with
      | nil => cases hLe
      | cons y ys =>
          exact congrArg Nat.succ (ih hLe.2)

theorem natListLe_nil_left {ys : List Nat}
    (hLe : NatListLe [] ys) :
    ys = [] := by
  cases ys with
  | nil => rfl
  | cons y ys => cases hLe

theorem natListLe_nil_right {xs : List Nat}
    (hLe : NatListLe xs []) :
    xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs => cases hLe

theorem natListLe_singleton_iff {x y : Nat} :
    NatListLe [x] [y] ↔ x ≤ y := by
  constructor
  · intro hLe
    exact hLe.1
  · intro hLe
    exact ⟨hLe, trivial⟩

end Pm4Lean
