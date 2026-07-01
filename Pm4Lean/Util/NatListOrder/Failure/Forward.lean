import Pm4Lean.Util.NatListOrder.Failure.Definition

namespace Pm4Lean

theorem natListLe_or_hasGreaterCoordinate_of_length_eq
    {xs ys : List Nat} (hLength : xs.length = ys.length) :
    NatListLe xs ys ∨ NatListHasGreaterCoordinate xs ys := by
  induction xs generalizing ys with
  | nil =>
      have hYs : ys = [] := List.eq_nil_of_length_eq_zero hLength.symm
      subst hYs
      exact Or.inl trivial
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases hLength
      | cons y ys =>
          have hTailLength : xs.length = ys.length := Nat.succ.inj hLength
          by_cases hHead : x ≤ y
          · obtain hTailLe | hTailGt := ih hTailLength
            · exact Or.inl ⟨hHead, hTailLe⟩
            · exact Or.inr (Or.inr hTailGt)
          · exact Or.inr (Or.inl (Nat.lt_of_not_ge hHead))

theorem natListHasGreaterCoordinate_of_not_natListLe
    {xs ys : List Nat}
    (hLength : xs.length = ys.length)
    (hNotLe : ¬ NatListLe xs ys) :
    NatListHasGreaterCoordinate xs ys := by
  obtain hLe | hGt :=
    natListLe_or_hasGreaterCoordinate_of_length_eq hLength
  · exact False.elim (hNotLe hLe)
  · exact hGt

end Pm4Lean
