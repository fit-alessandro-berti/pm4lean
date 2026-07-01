import Pm4Lean.Models.Petri.Basic.Marking.Support.TokenSum.Algebra

namespace Pm4Lean
namespace Petri

namespace Marking

variable {Place : Type u}

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

end Marking
end Petri
end Pm4Lean
