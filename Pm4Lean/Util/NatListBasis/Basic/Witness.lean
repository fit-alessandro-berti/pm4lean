import Pm4Lean.Util.NatListBasis.Basic.Escape

namespace Pm4Lean

theorem natListBasisHasGreaterCoordinateWitness_of_not_dominated
    {xs : List Nat} {basis : List (List Nat)}
    (hLength :
      ∀ upper : List Nat, upper ∈ basis → xs.length = upper.length)
    (hNotDominated : ¬ NatListDominatedBy xs basis) :
    NatListBasisHasGreaterCoordinateWitness xs basis := by
  intro upper hMem
  apply natListHasGreaterCoordinate_of_not_natListLe
    (hLength upper hMem)
  intro hLe
  exact hNotDominated (natListDominatedBy_of_mem_le hMem hLe)

theorem natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
    {xs : List Nat} {basis : List (List Nat)} {n : Nat}
    (hXsLength : xs.length = n)
    (hBasisLength :
      ∀ upper : List Nat, upper ∈ basis → upper.length = n)
    (hNotDominated : ¬ NatListDominatedBy xs basis) :
    NatListBasisHasGreaterCoordinateWitness xs basis :=
  natListBasisHasGreaterCoordinateWitness_of_not_dominated
    (fun upper hMem => by
      rw [hXsLength, hBasisLength upper hMem])
    hNotDominated

theorem natListBasisHasGreaterCoordinateWitness_singleton_iff
    {xs upper : List Nat} :
    NatListBasisHasGreaterCoordinateWitness xs [upper] ↔
      NatListHasGreaterCoordinate xs upper := by
  constructor
  · intro hWitness
    exact hWitness upper (List.Mem.head [])
  · intro hGreater candidate hCandidateMem
    cases hCandidateMem with
    | head =>
        exact hGreater
    | tail _ hTail =>
        cases hTail

theorem not_natListDominatedBy_of_basisGreaterCoordinateWitness
    {xs : List Nat} {basis : List (List Nat)}
    (hWitness : NatListBasisHasGreaterCoordinateWitness xs basis) :
    ¬ NatListDominatedBy xs basis := by
  intro hDominated
  obtain ⟨upper, hMem, hLe⟩ := hDominated
  exact not_natListLe_of_hasGreaterCoordinate (hWitness upper hMem) hLe

theorem not_natListDominatedBy_iff_basisGreaterCoordinateWitness
    {xs : List Nat} {basis : List (List Nat)}
    (hLength :
      ∀ upper : List Nat, upper ∈ basis → xs.length = upper.length) :
    ¬ NatListDominatedBy xs basis ↔
      NatListBasisHasGreaterCoordinateWitness xs basis :=
  ⟨natListBasisHasGreaterCoordinateWitness_of_not_dominated hLength,
    not_natListDominatedBy_of_basisGreaterCoordinateWitness⟩

end Pm4Lean
