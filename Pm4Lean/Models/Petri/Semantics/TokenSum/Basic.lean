import Pm4Lean.Models.Petri.Basic.Marking.Support
import Pm4Lean.Models.Petri.Semantics.FiringSequence

namespace Pm4Lean
namespace Petri

namespace Marking

theorem tokenSumOn_add {Place : Type u}
    (places : List Place) (M K : Marking Place) :
    TokenSumOn places (M + K) = TokenSumOn places M + TokenSumOn places K := by
  induction places with
  | nil =>
      simp [TokenSumOn]
  | cons p places ih =>
      rw [tokenSumOn_cons, tokenSumOn_cons, tokenSumOn_cons, add_apply, ih]
      omega

end Marking

theorem tokenSumOn_fire_le_add_post
    {N : Net} (places : List N.Place) (M : N.Marking) (t : N.Transition) :
    Marking.TokenSumOn places (fire N M t) ≤
      Marking.TokenSumOn places M + Marking.TokenSumOn places (N.post t) := by
  induction places with
  | nil =>
      simp [Marking.TokenSumOn]
  | cons p places ih =>
      rw [Marking.tokenSumOn_cons, Marking.tokenSumOn_cons,
        Marking.tokenSumOn_cons]
      have hHead : fire N M t p ≤ M p + N.post t p := by
        exact Nat.add_le_add_right (Nat.sub_le (M p) (N.pre t p)) (N.post t p)
      omega

theorem tokenSumOn_firingSequence_le_initial_add_length_mul_post_bound
    {N : Net} {M M' : N.Marking} {ts : List N.Transition} {c : Nat}
    (hPost : ∀ t : N.Transition,
      Marking.TokenSumOn N.places (N.post t) ≤ c)
    (hSeq : FiringSequence N M ts M') :
    Marking.TokenSumOn N.places M' ≤
      Marking.TokenSumOn N.places M + ts.length * c := by
  induction hSeq with
  | nil M =>
      simp
  | cons hEnabled hTail ih =>
      rename_i M M'' t ts
      have hFire :
          Marking.TokenSumOn N.places (fire N M t) ≤
            Marking.TokenSumOn N.places M + c :=
        Nat.le_trans
          (tokenSumOn_fire_le_add_post N.places M t)
          (Nat.add_le_add_left (hPost t) _)
      have hTailBound :
          Marking.TokenSumOn N.places M'' ≤
            Marking.TokenSumOn N.places (fire N M t) + ts.length * c :=
        ih
      have hCombined :
          Marking.TokenSumOn N.places M'' ≤
            (Marking.TokenSumOn N.places M + c) + ts.length * c :=
        Nat.le_trans hTailBound (Nat.add_le_add_right hFire _)
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hCombined

end Petri
end Pm4Lean
