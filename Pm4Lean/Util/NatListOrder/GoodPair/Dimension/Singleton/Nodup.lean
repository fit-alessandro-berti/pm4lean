import Pm4Lean.Util.NatListOrder.GoodPair.Dimension.Singleton.Lower

namespace Pm4Lean

theorem nodup_of_forall_singleton_not_containsNatListLePair
    {vectors : List (List Nat)}
    (hSingleton :
      ∀ xs : List Nat, xs ∈ vectors → ∃ x : Nat, xs = [x])
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    vectors.Nodup := by
  induction vectors with
  | nil =>
      exact List.nodup_nil
  | cons head tail ih =>
      have hHeadSingleton : ∃ x : Nat, head = [x] :=
        hSingleton head (List.Mem.head tail)
      obtain ⟨x, hHeadEq⟩ := hHeadSingleton
      subst hHeadEq
      have hTailSingleton :
          ∀ xs : List Nat, xs ∈ tail → ∃ x : Nat, xs = [x] := by
        intro xs hXsMem
        exact hSingleton xs (List.Mem.tail [x] hXsMem)
      have hNoTailPair : ¬ ContainsNatListLePair tail :=
        not_containsNatListLePair_tail_of_cons hNoPair
      refine List.nodup_cons.mpr ⟨?_, ih hTailSingleton hNoTailPair⟩
      intro hMem
      exact hNoPair
        (containsNatListLePair_cons_of_mem_le
          hMem
          (natListLe_refl [x]))

end Pm4Lean
