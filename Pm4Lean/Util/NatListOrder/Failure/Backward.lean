import Pm4Lean.Util.NatListOrder.Failure.Forward

namespace Pm4Lean

theorem not_natListLe_of_hasGreaterCoordinate
    {xs ys : List Nat}
    (hGt : NatListHasGreaterCoordinate xs ys) :
    ¬ NatListLe xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> intro hLe <;> cases hGt
  | cons x xs ih =>
      cases ys with
      | nil =>
          intro hLe
          cases hGt
      | cons y ys =>
          intro hLe
          cases hGt with
          | inl hHead =>
              exact Nat.not_lt_of_ge hLe.1 hHead
          | inr hTail =>
              exact ih hTail hLe.2

theorem not_natListLe_iff_hasGreaterCoordinate_of_length_eq
    {xs ys : List Nat} (hLength : xs.length = ys.length) :
    ¬ NatListLe xs ys ↔ NatListHasGreaterCoordinate xs ys :=
  ⟨natListHasGreaterCoordinate_of_not_natListLe hLength,
    not_natListLe_of_hasGreaterCoordinate⟩

end Pm4Lean
