import Pm4Lean.Util.NatListBasis.Greedy.Definition

namespace Pm4Lean

theorem natListGreedyBasisFrom_extends
    (vectors basis : List (List Nat)) :
    ∀ upper : List Nat, upper ∈ basis →
      upper ∈ natListGreedyBasisFrom vectors basis := by
  induction vectors generalizing basis with
  | nil =>
      intro upper hMem
      exact hMem
  | cons x xs ih =>
      intro upper hMem
      unfold natListGreedyBasisFrom
      by_cases hDominated : NatListDominatedBy x basis
      · simp [hDominated]
        exact ih basis upper hMem
      · simp [hDominated]
        exact ih (x :: basis) upper (List.Mem.tail x hMem)

theorem mem_natListGreedyBasisFrom
    {vectors basis : List (List Nat)} {upper : List Nat}
    (hMem : upper ∈ natListGreedyBasisFrom vectors basis) :
    upper ∈ basis ∨ upper ∈ vectors := by
  induction vectors generalizing basis with
  | nil =>
      exact Or.inl hMem
  | cons x xs ih =>
      unfold natListGreedyBasisFrom at hMem
      by_cases hDominated : NatListDominatedBy x basis
      · simp [hDominated] at hMem
        obtain hBasis | hXs := ih hMem
        · exact Or.inl hBasis
        · exact Or.inr (List.Mem.tail x hXs)
      · simp [hDominated] at hMem
        obtain hXBasis | hXs := ih hMem
        · cases hXBasis with
          | head =>
              exact Or.inr (List.Mem.head xs)
          | tail _ hBasis =>
              exact Or.inl hBasis
        · exact Or.inr (List.Mem.tail x hXs)

theorem mem_natListGreedyBasis
    {vectors : List (List Nat)} {upper : List Nat}
    (hMem : upper ∈ natListGreedyBasis vectors) :
    upper ∈ vectors := by
  have h := mem_natListGreedyBasisFrom
    (vectors := vectors) (basis := []) hMem
  cases h with
  | inl hNil =>
      cases hNil
  | inr hVectors =>
      exact hVectors

end Pm4Lean
