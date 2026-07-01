import Pm4Lean.Util.NatListOrder

namespace Pm4Lean

def NatListDominatedBy (xs : List Nat) (basis : List (List Nat)) : Prop :=
  ∃ upper : List Nat, upper ∈ basis ∧ NatListLe xs upper

def NatListBasisHasGreaterCoordinateWitness
    (xs : List Nat) (basis : List (List Nat)) : Prop :=
  ∀ upper : List Nat, upper ∈ basis →
    NatListHasGreaterCoordinate xs upper

theorem natListDominatedBy_of_mem
    {xs : List Nat} {basis : List (List Nat)}
    (hMem : xs ∈ basis) :
    NatListDominatedBy xs basis :=
  ⟨xs, hMem, natListLe_refl xs⟩

theorem natListDominatedBy_of_mem_le
    {xs upper : List Nat} {basis : List (List Nat)}
    (hMem : upper ∈ basis)
    (hLe : NatListLe xs upper) :
    NatListDominatedBy xs basis :=
  ⟨upper, hMem, hLe⟩

theorem natListDominatedBy_singleton_iff
    {xs upper : List Nat} :
    NatListDominatedBy xs [upper] ↔ NatListLe xs upper := by
  constructor
  · intro hDominated
    obtain ⟨candidate, hCandidateMem, hLe⟩ := hDominated
    cases hCandidateMem with
    | head =>
        exact hLe
    | tail _ hTail =>
        cases hTail
  · intro hLe
    exact natListDominatedBy_of_mem_le (List.Mem.head []) hLe

theorem not_natListDominatedBy_singleton_iff
    {xs upper : List Nat} :
    ¬ NatListDominatedBy xs [upper] ↔ ¬ NatListLe xs upper := by
  constructor
  · intro hNotDominated hLe
    exact hNotDominated (natListDominatedBy_singleton_iff.mpr hLe)
  · intro hNotLe hDominated
    exact hNotLe (natListDominatedBy_singleton_iff.mp hDominated)

theorem not_mem_of_not_natListDominatedBy
    {xs : List Nat} {basis : List (List Nat)}
    (hNotDominated : ¬ NatListDominatedBy xs basis) :
    xs ∉ basis := by
  intro hMem
  exact hNotDominated (natListDominatedBy_of_mem hMem)

end Pm4Lean
