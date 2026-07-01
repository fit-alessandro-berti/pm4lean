import Pm4Lean.Util.NatListBasis.Coverage
import Pm4Lean.Util.NatListBasis.Greedy.Dominates

namespace Pm4Lean

theorem natListDominatedBy_trans_basis
    {xs : List Nat} {basis basis' : List (List Nat)}
    (hBasisDominated : NatListBasisDominatesAll basis basis')
    (hDominated : NatListDominatedBy xs basis) :
    NatListDominatedBy xs basis' := by
  obtain ⟨upper, hMem, hLe⟩ := hDominated
  obtain ⟨upper', hUpperMem, hUpperLe⟩ :=
    hBasisDominated upper hMem
  exact ⟨upper', hUpperMem, natListLe_trans hLe hUpperLe⟩

theorem natListBasisDominatesAll_trans
    {vectors basis basis' : List (List Nat)}
    (hBasisDominated : NatListBasisDominatesAll basis basis')
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll vectors basis' := by
  intro xs hMem
  exact natListDominatedBy_trans_basis
    hBasisDominated
    (hDominates xs hMem)

theorem natListBasisDominatesAll_greedy_of_dominatedBy
    {vectors basis : List (List Nat)}
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll (natListGreedyBasis vectors) basis := by
  intro xs hMem
  exact hDominates xs (mem_natListGreedyBasis hMem)

theorem natListBasisDominatesAll_of_greedy_dominated
    {vectors basis : List (List Nat)}
    (hGreedyDominated :
      NatListBasisDominatesAll (natListGreedyBasis vectors) basis) :
    NatListBasisDominatesAll vectors basis :=
  natListBasisDominatesAll_trans
    hGreedyDominated
    (natListGreedyBasis_dominatesAll vectors)

end Pm4Lean
