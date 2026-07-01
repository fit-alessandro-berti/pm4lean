import Pm4Lean.Util.NatListBasis.Greedy.Membership

namespace Pm4Lean

theorem natListGreedyBasisFrom_cons_of_dominated
    {x : List Nat} {xs basis : List (List Nat)}
    (hDominated : NatListDominatedBy x basis) :
    natListGreedyBasisFrom (x :: xs) basis =
      natListGreedyBasisFrom xs basis := by
  classical
  change
    (if NatListDominatedBy x basis then
      natListGreedyBasisFrom xs basis
    else
      natListGreedyBasisFrom xs (x :: basis)) =
        natListGreedyBasisFrom xs basis
  simp [hDominated]

theorem natListGreedyBasisFrom_cons_of_not_dominated
    {x : List Nat} {xs basis : List (List Nat)}
    (hNotDominated : ¬ NatListDominatedBy x basis) :
    natListGreedyBasisFrom (x :: xs) basis =
      natListGreedyBasisFrom xs (x :: basis) := by
  classical
  change
    (if NatListDominatedBy x basis then
      natListGreedyBasisFrom xs basis
    else
      natListGreedyBasisFrom xs (x :: basis)) =
        natListGreedyBasisFrom xs (x :: basis)
  simp [hNotDominated]

theorem mem_natListGreedyBasisFrom_cons_self_of_not_dominated
    {x : List Nat} {xs basis : List (List Nat)}
    (hNotDominated : ¬ NatListDominatedBy x basis) :
    x ∈ natListGreedyBasisFrom (x :: xs) basis := by
  rw [natListGreedyBasisFrom_cons_of_not_dominated hNotDominated]
  exact natListGreedyBasisFrom_extends xs (x :: basis) x (List.Mem.head basis)

theorem natListGreedyBasisFrom_cons_self_witness_of_not_dominated
    {x : List Nat} {xs basis : List (List Nat)}
    (hNotDominated : ¬ NatListDominatedBy x basis) :
    x ∈ natListGreedyBasisFrom (x :: xs) basis ∧
      ¬ NatListDominatedBy x basis :=
  ⟨mem_natListGreedyBasisFrom_cons_self_of_not_dominated hNotDominated,
    hNotDominated⟩

end Pm4Lean
