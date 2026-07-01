import Pm4Lean.Util.NatListBasis.Greedy.Membership

namespace Pm4Lean

theorem natListDominatedBy_greedyBasisFrom_of_basis
    {vectors basis : List (List Nat)} {x : List Nat}
    (hDominated : NatListDominatedBy x basis) :
    NatListDominatedBy x (natListGreedyBasisFrom vectors basis) :=
  natListDominatedBy_of_basis_subset
    (natListGreedyBasisFrom_extends vectors basis)
    hDominated

theorem natListGreedyBasisFrom_dominatesAll
    (vectors basis : List (List Nat)) :
    NatListBasisDominatesAll vectors
      (natListGreedyBasisFrom vectors basis) := by
  induction vectors generalizing basis with
  | nil =>
      exact natListBasisDominatesAll_nil
        (natListGreedyBasisFrom [] basis)
  | cons x xs ih =>
      unfold natListGreedyBasisFrom
      by_cases hDominated : NatListDominatedBy x basis
      · simp [hDominated]
        intro ys hMem
        cases hMem with
        | head =>
            exact natListDominatedBy_greedyBasisFrom_of_basis
              (vectors := xs) hDominated
        | tail _ hTail =>
            exact ih basis ys hTail
      · simp [hDominated]
        intro ys hMem
        cases hMem with
        | head =>
            exact natListDominatedBy_of_mem_le
              (natListGreedyBasisFrom_extends xs (x :: basis)
                x (List.Mem.head basis))
              (natListLe_refl x)
        | tail _ hTail =>
            exact ih (x :: basis) ys hTail

theorem natListGreedyBasis_dominatesAll
    (vectors : List (List Nat)) :
    NatListBasisDominatesAll vectors (natListGreedyBasis vectors) :=
  natListGreedyBasisFrom_dominatesAll vectors []

end Pm4Lean
