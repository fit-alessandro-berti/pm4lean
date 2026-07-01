import Pm4Lean.Util.List.Finiteness
import Pm4Lean.Util.NatListOrder.GoodPair.Base

namespace Pm4Lean

theorem length_le_one_of_forall_length_zero_not_containsNatListLePair
    {vectors : List (List Nat)}
    (hLength : ∀ x : List Nat, x ∈ vectors → x.length = 0)
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    vectors.length ≤ 1 := by
  cases vectors with
  | nil =>
      simp
  | cons x vectors =>
      cases vectors with
      | nil =>
          simp
      | cons y ys =>
          have hXNil : x = [] :=
            List.eq_nil_of_length_eq_zero
              (hLength x (List.Mem.head (y :: ys)))
          have hYNil : y = [] :=
            List.eq_nil_of_length_eq_zero
              (hLength y (List.Mem.tail x (List.Mem.head ys)))
          subst hXNil
          subst hYNil
          exact False.elim
            (hNoPair
              (containsNatListLePair_cons_of_mem_le
                (List.Mem.head ys)
                (natListLe_refl [])))

end Pm4Lean
