import Pm4Lean.Models.Petri.Basic.Marking

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

/-- Sum the tokens of a marking over a finite list of places. -/
def TokenSumOn (places : List Place) (M : Marking Place) : Nat :=
  places.foldl (fun acc p => acc + M p) 0

/-- A marking has no tokens outside a finite list of places. -/
def EmptyOutside (places : List Place) (M : Marking Place) : Prop :=
  ∀ p : Place, p ∉ places → M p = 0

theorem tokenSumOn_nil (M : Marking Place) :
    TokenSumOn [] M = 0 :=
  rfl

theorem tokenSumOn_singleton (p : Place) (M : Marking Place) :
    TokenSumOn [p] M = M p := by
  simp [TokenSumOn]

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

theorem le_tokenSumOn_of_mem {places : List Place} {M : Marking Place}
    {p : Place} (hMem : p ∈ places) :
    M p ≤ TokenSumOn places M := by
  induction places with
  | nil =>
      cases hMem
  | cons q places ih =>
      rw [tokenSumOn_cons]
      cases hMem with
      | head =>
          exact Nat.le_add_right (M p) (TokenSumOn places M)
      | tail _ hTail =>
          exact Nat.le_trans (ih hTail) (Nat.le_add_left _ _)

theorem le_tokenSumOn_of_complete (places : List Place)
    (hComplete : ∀ p : Place, p ∈ places) (M : Marking Place)
    (p : Place) :
    M p ≤ TokenSumOn places M :=
  le_tokenSumOn_of_mem (M := M) (hComplete p)

theorem tokenSumOn_le_length_mul_of_forall_mem_le
    {places : List Place} {M : Marking Place} {k : Nat}
    (hBound : ∀ p : Place, p ∈ places → M p ≤ k) :
    TokenSumOn places M ≤ places.length * k := by
  induction places with
  | nil =>
      simp [TokenSumOn]
  | cons p places ih =>
      have hHead : M p ≤ k :=
        hBound p (List.Mem.head places)
      have hTail : TokenSumOn places M ≤ places.length * k :=
        ih (fun q hMem => hBound q (List.Mem.tail p hMem))
      have hSum : M p + TokenSumOn places M ≤ k + places.length * k :=
        Nat.add_le_add hHead hTail
      simpa [tokenSumOn_cons, Nat.succ_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hSum

theorem tokenSumOn_le_length_mul_of_forall_le
    (places : List Place) (M : Marking Place) (k : Nat)
    (hBound : ∀ p : Place, M p ≤ k) :
    TokenSumOn places M ≤ places.length * k :=
  tokenSumOn_le_length_mul_of_forall_mem_le
    (M := M) (k := k) (fun p _hMem => hBound p)

theorem emptyOutside_nil_iff (M : Marking Place) :
    EmptyOutside [] M ↔ M = zero := by
  constructor
  · intro h
    apply ext
    intro p
    exact h p (by simp)
  · intro h p _hp
    rw [h]
    rfl

theorem emptyOutside_of_subset {support allowed : List Place}
    {M : Marking Place}
    (hSubset : ∀ p : Place, p ∈ support → p ∈ allowed)
    (hEmpty : EmptyOutside support M) :
    EmptyOutside allowed M := by
  intro p hpNotInPlaces
  apply hEmpty
  intro hpInSupport
  exact hpNotInPlaces (hSubset p hpInSupport)

theorem emptyOutside_zero (places : List Place) :
    EmptyOutside places (zero : Marking Place) := by
  intro _p _h
  rfl

end Marking
end Petri
end Pm4Lean
