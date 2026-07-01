import Pm4Lean.Util.List.Relation
import Pm4Lean.Util.NatListOrder.Core

namespace Pm4Lean

def ContainsNatListLePair (vectors : List (List Nat)) : Prop :=
  List.ContainsRelatedPair NatListLe vectors

theorem containsNatListLePair_cons_of_mem_le
    {x y : List Nat} {vectors : List (List Nat)}
    (hMem : y ∈ vectors) (hLe : NatListLe x y) :
    ContainsNatListLePair (x :: vectors) :=
  List.containsRelatedPair_cons_of_mem_related hMem hLe

theorem containsNatListLePair_cons_tail
    {x : List Nat} {vectors : List (List Nat)}
    (hPair : ContainsNatListLePair vectors) :
    ContainsNatListLePair (x :: vectors) :=
  List.containsRelatedPair_cons_tail hPair

theorem containsNatListLePair_map_cons_of_containsNatListLePair
    {x : Nat} {vectors : List (List Nat)}
    (hPair : ContainsNatListLePair vectors) :
    ContainsNatListLePair (vectors.map (fun xs => x :: xs)) :=
  List.containsRelatedPair_map hPair
    (fun hLe => natListLe_cons (Nat.le_refl x) hLe)

theorem not_containsNatListLePair_tail_of_cons
    {x : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair (x :: vectors)) :
    ¬ ContainsNatListLePair vectors :=
  List.not_containsRelatedPair_tail_of_cons hNoPair

theorem not_containsNatListLePair_of_not_map_cons
    {x : Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair
      (vectors.map (fun xs => x :: xs))) :
    ¬ ContainsNatListLePair vectors := by
  intro hPair
  exact hNoPair
    (containsNatListLePair_map_cons_of_containsNatListLePair hPair)

theorem not_natListLe_head_of_not_containsNatListLePair_cons
    {x y : List Nat} {vectors : List (List Nat)}
    (hNoPair : ¬ ContainsNatListLePair (x :: vectors))
    (hMem : y ∈ vectors) :
    ¬ NatListLe x y :=
  List.not_related_head_of_not_containsRelatedPair_cons hNoPair hMem

end Pm4Lean
