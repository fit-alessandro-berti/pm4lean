import Pm4Lean.Util.NatListBasis.Greedy.Append.Scan

namespace Pm4Lean

theorem mem_natListGreedyBasisFrom_append_cons_self_of_not_dominated
    {pre suffix basis : List (List Nat)} {x : List Nat}
    (hNotDominated :
      ¬ NatListDominatedBy x
        (natListGreedyBasisFrom pre basis)) :
    x ∈ natListGreedyBasisFrom (pre ++ x :: suffix) basis := by
  rw [natListGreedyBasisFrom_append pre (x :: suffix) basis]
  exact mem_natListGreedyBasisFrom_cons_self_of_not_dominated hNotDominated

theorem natListGreedyBasisFrom_append_cons_self_witness_of_not_dominated
    {pre suffix basis : List (List Nat)} {x : List Nat}
    (hNotDominated :
      ¬ NatListDominatedBy x
        (natListGreedyBasisFrom pre basis)) :
    x ∈ natListGreedyBasisFrom (pre ++ x :: suffix) basis ∧
      ¬ NatListDominatedBy x (natListGreedyBasisFrom pre basis) :=
  ⟨mem_natListGreedyBasisFrom_append_cons_self_of_not_dominated
      hNotDominated,
    hNotDominated⟩

theorem not_natListLe_of_mem_greedyBasisFrom_of_not_dominated
    {pre basis : List (List Nat)} {x y : List Nat}
    (hYMem : y ∈ natListGreedyBasisFrom pre basis)
    (hNotDominated :
      ¬ NatListDominatedBy x (natListGreedyBasisFrom pre basis)) :
    ¬ NatListLe x y := by
  intro hLe
  exact hNotDominated (natListDominatedBy_of_mem_le hYMem hLe)

theorem natListHasGreaterCoordinate_of_mem_greedyBasisFrom_of_not_dominated
    {pre basis : List (List Nat)} {x y : List Nat}
    (hYMem : y ∈ natListGreedyBasisFrom pre basis)
    (hLength : x.length = y.length)
    (hNotDominated :
      ¬ NatListDominatedBy x (natListGreedyBasisFrom pre basis)) :
    NatListHasGreaterCoordinate x y :=
  natListHasGreaterCoordinate_of_not_natListLe hLength
    (not_natListLe_of_mem_greedyBasisFrom_of_not_dominated
      hYMem hNotDominated)

end Pm4Lean
