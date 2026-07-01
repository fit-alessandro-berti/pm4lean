import Pm4Lean.Util.NatListOrder.GoodPair.Base.Pairwise.Duplicate

namespace Pm4Lean

theorem containsNatListLePair_iff_not_pairwise_not_natListLe
    {vectors : List (List Nat)} :
    ContainsNatListLePair vectors ↔
      ¬ List.Pairwise (fun xs ys => ¬ NatListLe xs ys) vectors :=
  List.containsRelatedPair_iff_not_pairwise_not

theorem not_containsNatListLePair_iff_pairwise_not_natListLe
    {vectors : List (List Nat)} :
    ¬ ContainsNatListLePair vectors ↔
      List.Pairwise (fun xs ys => ¬ NatListLe xs ys) vectors := by
  constructor
  · intro hNoPair
    exact Classical.byContradiction (fun hNotPairwise =>
      hNoPair
        (containsNatListLePair_iff_not_pairwise_not_natListLe.mpr
          hNotPairwise))
  · intro hPairwise hPair
    exact
      (containsNatListLePair_iff_not_pairwise_not_natListLe.mp hPair)
        hPairwise

end Pm4Lean
