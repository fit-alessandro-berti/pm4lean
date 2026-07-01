import Pm4Lean.Util.NatListOrder.GoodPair.Base.Pairwise.Equiv

namespace Pm4Lean

theorem pairwise_not_natListLe_map_cons_of_pairwise_not_natListLe
    {x : Nat} {vectors : List (List Nat)}
    (hPairwise :
      List.Pairwise (fun xs ys => ¬ NatListLe xs ys) vectors) :
    List.Pairwise (fun xs ys => ¬ NatListLe xs ys)
      (vectors.map (fun xs => x :: xs)) := by
  induction vectors with
  | nil =>
      exact List.Pairwise.nil
  | cons head tail ih =>
      rw [List.pairwise_cons] at hPairwise
      exact List.Pairwise.cons
        (fun y hYMem hLe =>
          let ⟨tailVector, hTailMem, hTailEq⟩ := List.mem_map.mp hYMem
          hPairwise.1 tailVector hTailMem
            (natListLe_tail_of_cons (by
              rw [← hTailEq] at hLe
              exact hLe)))
        (ih hPairwise.2)

theorem not_containsNatListLePair_map_cons_of_not_containsNatListLePair
    {x : Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    ¬ ContainsNatListLePair (vectors.map (fun xs => x :: xs)) :=
  not_containsNatListLePair_iff_pairwise_not_natListLe.mpr
    (pairwise_not_natListLe_map_cons_of_pairwise_not_natListLe
      (not_containsNatListLePair_iff_pairwise_not_natListLe.mp hNoPair))

theorem containsNatListLePair_of_containsNatListLePair_map_cons
    {x : Nat} {vectors : List (List Nat)}
    (hPair : ContainsNatListLePair
      (vectors.map (fun xs => x :: xs))) :
    ContainsNatListLePair vectors :=
  Classical.byContradiction (fun hNoPair =>
    not_containsNatListLePair_map_cons_of_not_containsNatListLePair hNoPair
      hPair)

theorem containsNatListLePair_map_cons_iff
    {x : Nat} {vectors : List (List Nat)} :
    ContainsNatListLePair (vectors.map (fun xs => x :: xs)) ↔
      ContainsNatListLePair vectors :=
  ⟨containsNatListLePair_of_containsNatListLePair_map_cons,
    containsNatListLePair_map_cons_of_containsNatListLePair⟩

end Pm4Lean
