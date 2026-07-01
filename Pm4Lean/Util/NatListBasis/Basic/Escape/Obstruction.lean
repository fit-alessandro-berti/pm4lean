import Pm4Lean.Util.NatListBasis.Basic.Escape.Construction
import Pm4Lean.Util.NatListMax

namespace Pm4Lean

theorem exists_singleton_not_dominatedBy_basis
    (basis : List (List Nat)) :
    ∃ x : Nat, ¬ NatListDominatedBy [x] basis := by
  refine ⟨NatListMax basis.flatten + 1, ?_⟩
  intro hDominated
  obtain ⟨upper, hUpperMem, hLe⟩ := hDominated
  cases upper with
  | nil =>
      cases hLe
  | cons y tail =>
      have hTailNil : tail = [] :=
        natListLe_nil_left hLe.2
      subst hTailNil
      have hYMemFlatten : y ∈ basis.flatten := by
        rw [List.mem_flatten]
        exact ⟨[y], hUpperMem, List.Mem.head []⟩
      exact Nat.not_succ_le_self (NatListMax basis.flatten)
        (Nat.le_trans hLe.1 (le_natListMax_of_mem hYMemFlatten))

theorem exists_not_containsNatListLePair_singletons
    (n : Nat) :
    ∃ vectors : List (List Nat),
      vectors.length = n ∧
        (∀ xs : List Nat, xs ∈ vectors → xs.length = 1) ∧
        ¬ ContainsNatListLePair vectors := by
  apply exists_not_containsNatListLePair_list_of_forall_basis_escape
    (P := fun xs : List Nat => xs.length = 1)
  intro basis
  obtain ⟨x, hNotDominated⟩ := exists_singleton_not_dominatedBy_basis basis
  exact ⟨[x], rfl, hNotDominated⟩

end Pm4Lean
