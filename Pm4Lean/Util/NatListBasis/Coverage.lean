import Pm4Lean.Util.NatListBasis.Basic

namespace Pm4Lean

def NatListBasisDominatesAll
    (vectors basis : List (List Nat)) : Prop :=
  ∀ xs : List Nat, xs ∈ vectors → NatListDominatedBy xs basis

theorem natListBasisDominatesAll_nil
    (basis : List (List Nat)) :
    NatListBasisDominatesAll [] basis := by
  intro xs hMem
  cases hMem

theorem natListBasisDominatesAll_self
    (vectors : List (List Nat)) :
    NatListBasisDominatesAll vectors vectors := by
  intro xs hMem
  exact natListDominatedBy_of_mem hMem

theorem natListDominatedBy_of_basis_subset
    {xs : List Nat} {basis basis' : List (List Nat)}
    (hSubset : ∀ upper : List Nat, upper ∈ basis → upper ∈ basis')
    (hDominated : NatListDominatedBy xs basis) :
    NatListDominatedBy xs basis' := by
  obtain ⟨upper, hMem, hLe⟩ := hDominated
  exact ⟨upper, hSubset upper hMem, hLe⟩

theorem natListBasisDominatesAll_of_basis_subset
    {vectors basis basis' : List (List Nat)}
    (hSubset : ∀ upper : List Nat, upper ∈ basis → upper ∈ basis')
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll vectors basis' := by
  intro xs hMem
  exact natListDominatedBy_of_basis_subset hSubset (hDominates xs hMem)

theorem natListBasisDominatesAll_cons_of_dominated
    {x : List Nat} {vectors basis : List (List Nat)}
    (hX : NatListDominatedBy x basis)
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll (x :: vectors) basis := by
  intro ys hMem
  cases hMem with
  | head =>
      exact hX
  | tail _ hTail =>
      exact hDominates ys hTail

theorem natListBasisDominatesAll_cons_basis
    {x : List Nat} {vectors basis : List (List Nat)}
    (hDominates : NatListBasisDominatesAll vectors basis) :
    NatListBasisDominatesAll (x :: vectors) (x :: basis) := by
  intro ys hMem
  cases hMem with
  | head =>
      exact natListDominatedBy_of_mem (List.Mem.head basis)
  | tail _ hTail =>
      exact natListDominatedBy_of_basis_subset
        (fun upper hUpperMem => List.Mem.tail x hUpperMem)
        (hDominates ys hTail)

end Pm4Lean
