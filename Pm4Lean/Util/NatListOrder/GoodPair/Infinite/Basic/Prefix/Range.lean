import Init.Data.List.Nat.Pairwise
import Pm4Lean.Util.NatListOrder.GoodPair.Base.Pairwise
import Pm4Lean.Util.NatListOrder.GoodPair.Infinite.Basic.Definition

namespace Pm4Lean

theorem pairwise_lt_range (n : Nat) :
    List.Pairwise (fun i j : Nat => i < j) (List.range n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.pairwise_append]
      refine ⟨ih, ?_, ?_⟩
      · simp
      · intro i hIMem j hJMem
        simp at hJMem
        subst hJMem
        exact List.mem_range.mp hIMem

theorem pairwise_map_range_of_forall_lt
    {α : Type u} {R : α → α → Prop} {f : Nat → α} {n : Nat}
    (hRel : ∀ i j : Nat, i < j → R (f i) (f j)) :
    List.Pairwise R ((List.range n).map f) := by
  rw [List.pairwise_map]
  exact (pairwise_lt_range n).imp
    (fun hLt => hRel _ _ hLt)

theorem not_containsNatListLePair_map_range_of_forall_not
    {f : Nat → List Nat} {n : Nat}
    (hNoLe :
      ∀ i j : Nat, i < j → ¬ NatListLe (f i) (f j)) :
    ¬ ContainsNatListLePair ((List.range n).map f) :=
  not_containsNatListLePair_iff_pairwise_not_natListLe.mpr
    (pairwise_map_range_of_forall_lt hNoLe)

end Pm4Lean
