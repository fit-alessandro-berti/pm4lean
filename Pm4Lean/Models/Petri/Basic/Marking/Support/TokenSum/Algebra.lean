import Pm4Lean.Models.Petri.Basic.Marking.Support.TokenSum.Definition

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

theorem tokenSumOn_foldl_eq_add
    (places : List Place) (M : Marking Place) (acc : Nat) :
    places.foldl (fun acc p => acc + M p) acc =
      acc + TokenSumOn places M := by
  induction places generalizing acc with
  | nil =>
      simp [TokenSumOn]
  | cons p places ih =>
      calc
        (p :: places).foldl (fun acc q => acc + M q) acc
            = places.foldl (fun acc q => acc + M q) (acc + M p) := rfl
        _ = (acc + M p) + TokenSumOn places M := ih (acc + M p)
        _ = acc + (M p + TokenSumOn places M) := by
          rw [Nat.add_assoc]
        _ = acc + places.foldl (fun acc q => acc + M q) (0 + M p) := by
          rw [ih (0 + M p), Nat.zero_add]
        _ = acc + TokenSumOn (p :: places) M := rfl

theorem tokenSumOn_cons (p : Place) (places : List Place)
    (M : Marking Place) :
    TokenSumOn (p :: places) M = M p + TokenSumOn places M := by
  calc
    TokenSumOn (p :: places) M
        = places.foldl (fun acc q => acc + M q) (0 + M p) := rfl
    _ = (0 + M p) + TokenSumOn places M :=
      tokenSumOn_foldl_eq_add places M (0 + M p)
    _ = M p + TokenSumOn places M := by rw [Nat.zero_add]

theorem tokenSumOn_append (left right : List Place) (M : Marking Place) :
    TokenSumOn (left ++ right) M =
      TokenSumOn left M + TokenSumOn right M := by
  induction left with
  | nil =>
      simp [TokenSumOn]
  | cons p left ih =>
      rw [List.cons_append, tokenSumOn_cons, ih, tokenSumOn_cons,
        Nat.add_assoc]

end Marking
end Petri
end Pm4Lean
