import Pm4Lean.Util.NatListBasis.Greedy.Step

namespace Pm4Lean

theorem natListGreedyBasisFrom_append
    (pre suffix basis : List (List Nat)) :
    natListGreedyBasisFrom (pre ++ suffix) basis =
      natListGreedyBasisFrom suffix
        (natListGreedyBasisFrom pre basis) := by
  induction pre generalizing basis with
  | nil =>
      rfl
  | cons x xs ih =>
      change
        natListGreedyBasisFrom (x :: (xs ++ suffix)) basis =
          natListGreedyBasisFrom suffix
            (natListGreedyBasisFrom (x :: xs) basis)
      by_cases hDominated : NatListDominatedBy x basis
      · rw [natListGreedyBasisFrom_cons_of_dominated
          (x := x) (xs := xs ++ suffix) (basis := basis) hDominated,
          natListGreedyBasisFrom_cons_of_dominated
          (x := x) (xs := xs) (basis := basis) hDominated]
        exact ih basis
      · rw [natListGreedyBasisFrom_cons_of_not_dominated
          (x := x) (xs := xs ++ suffix) (basis := basis) hDominated,
          natListGreedyBasisFrom_cons_of_not_dominated
          (x := x) (xs := xs) (basis := basis) hDominated]
        exact ih (x :: basis)

end Pm4Lean
