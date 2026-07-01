import Pm4Lean.Util.NatListOrder.Core.Definition

namespace Pm4Lean

theorem natListLe_refl (ns : List Nat) :
    NatListLe ns ns := by
  induction ns with
  | nil =>
      trivial
  | cons n ns ih =>
      exact ⟨Nat.le_refl n, ih⟩

theorem natListLe_trans {xs ys zs : List Nat}
    (hXY : NatListLe xs ys) (hYZ : NatListLe ys zs) :
    NatListLe xs zs := by
  induction xs generalizing ys zs with
  | nil =>
      cases ys with
      | nil =>
          cases zs with
          | nil => trivial
          | cons z zs => cases hYZ
      | cons y ys => cases hXY
  | cons x xs ih =>
      cases ys with
      | nil => cases hXY
      | cons y ys =>
          cases zs with
          | nil => cases hYZ
          | cons z zs =>
              exact ⟨Nat.le_trans hXY.1 hYZ.1, ih hXY.2 hYZ.2⟩

end Pm4Lean
