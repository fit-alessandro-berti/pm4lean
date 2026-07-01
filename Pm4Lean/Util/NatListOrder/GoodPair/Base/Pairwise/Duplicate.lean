import Pm4Lean.Util.NatListOrder.GoodPair.Base.Head

namespace Pm4Lean

theorem not_containsDuplicatePair_of_not_containsNatListLePair
    {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    ¬ List.ContainsDuplicatePair vectors := by
  intro hDuplicate
  obtain ⟨x, before, between, after, hSplit⟩ := hDuplicate
  exact hNoPair
    ⟨x, x, before, between, after, hSplit, natListLe_refl x⟩

theorem containsNatListLePair_of_containsDuplicatePair
    {vectors : List (List Nat)}
    (hDuplicate : List.ContainsDuplicatePair vectors) :
    ContainsNatListLePair vectors := by
  obtain ⟨x, before, between, after, hSplit⟩ := hDuplicate
  exact ⟨x, x, before, between, after, hSplit, natListLe_refl x⟩

theorem nodup_of_not_containsNatListLePair
    {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair vectors) :
    vectors.Nodup :=
  Classical.byContradiction (fun hNotNodup =>
    not_containsDuplicatePair_of_not_containsNatListLePair hNoPair
      (List.containsDuplicatePair_of_not_nodup hNotNodup))

end Pm4Lean
