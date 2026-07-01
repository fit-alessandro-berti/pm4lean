import Pm4Lean.Util.NatListOrder.Core

namespace Pm4Lean

theorem natListLe_append {xs ys xs' ys' : List Nat}
    (hLe : NatListLe xs ys) (hLe' : NatListLe xs' ys') :
    NatListLe (xs ++ xs') (ys ++ ys') := by
  induction xs generalizing ys with
  | nil =>
      have hYs : ys = [] := natListLe_nil_left hLe
      subst hYs
      exact hLe'
  | cons x xs ih =>
      cases ys with
      | nil => cases hLe
      | cons y ys =>
          exact ⟨hLe.1, ih hLe.2⟩

end Pm4Lean
