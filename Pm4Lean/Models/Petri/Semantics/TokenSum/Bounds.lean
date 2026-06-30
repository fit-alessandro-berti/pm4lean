import Pm4Lean.Models.Petri.Semantics.TokenSum.Basic

namespace Pm4Lean
namespace Petri

def TransitionPostTokenBoundFrom (N : Net) :
    List N.Transition → Nat
  | [] => 0
  | t :: transitions =>
      Nat.max
        (Marking.TokenSumOn N.places (N.post t))
        (TransitionPostTokenBoundFrom N transitions)

def TransitionPostTokenBound (N : Net) : Nat :=
  TransitionPostTokenBoundFrom N N.transitions

theorem transitionPostTokenBoundFrom_le
    {N : Net} {transitions : List N.Transition} {t : N.Transition}
    (hMem : t ∈ transitions) :
    Marking.TokenSumOn N.places (N.post t) ≤
      TransitionPostTokenBoundFrom N transitions := by
  induction transitions with
  | nil =>
      cases hMem
  | cons u transitions ih =>
      cases hMem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ hTail =>
          exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)

theorem post_tokenSum_le_transitionPostTokenBound
    (N : Net) (t : N.Transition) :
    Marking.TokenSumOn N.places (N.post t) ≤
      TransitionPostTokenBound N := by
  exact transitionPostTokenBoundFrom_le
    (N := N) (N.transitions_complete t)

theorem length_gt_of_tokenSum_gt_initial_add_post_bound
    {N : Net} {M M' : N.Marking} {ts : List N.Transition} {n c : Nat}
    (hPost : ∀ t : N.Transition,
      Marking.TokenSumOn N.places (N.post t) ≤ c)
    (hSeq : FiringSequence N M ts M')
    (hLarge :
      Marking.TokenSumOn N.places M + n * c <
        Marking.TokenSumOn N.places M') :
    n < ts.length := by
  by_cases hGoal : n < ts.length
  · exact hGoal
  have hLenLe : ts.length ≤ n :=
    Nat.le_of_not_gt hGoal
  have hSeqBound :
      Marking.TokenSumOn N.places M' ≤
        Marking.TokenSumOn N.places M + ts.length * c :=
    tokenSumOn_firingSequence_le_initial_add_length_mul_post_bound
      hPost hSeq
  have hLenBound :
      Marking.TokenSumOn N.places M + ts.length * c ≤
        Marking.TokenSumOn N.places M + n * c :=
    Nat.add_le_add_left (Nat.mul_le_mul_right c hLenLe) _
  exact False.elim
    ((Nat.not_lt_of_ge (Nat.le_trans hSeqBound hLenBound)) hLarge)

end Petri
end Pm4Lean
