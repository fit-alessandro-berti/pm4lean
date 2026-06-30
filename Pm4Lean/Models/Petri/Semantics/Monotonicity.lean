import Pm4Lean.Models.Petri.Semantics.Reachability

namespace Pm4Lean
namespace Petri

theorem enabled_add_right
    {N : Net} {M : N.Marking} (K : N.Marking) {t : N.Transition}
    (hEnabled : Enabled N M t) :
    Enabled N (M + K) t := by
  intro p
  exact Nat.le_trans (hEnabled p) (Nat.le_add_right (M p) (K p))

theorem fire_add_right_of_enabled
    {N : Net} {M : N.Marking} (K : N.Marking) {t : N.Transition}
    (hEnabled : Enabled N M t) :
    fire N (M + K) t = fire N M t + K := by
  apply Marking.ext
  intro p
  calc
    fire N (M + K) t p =
        (M p + K p) - N.pre t p + N.post t p := rfl
    _ = (M p - N.pre t p + K p) + N.post t p := by
        rw [Nat.sub_add_comm (hEnabled p)]
    _ = M p - N.pre t p + N.post t p + K p := by
        rw [Nat.add_right_comm]
    _ = (fire N M t + K) p := rfl

namespace FiringSequence

theorem add_right
    {N : Net} {M M' : N.Marking} {ts : List N.Transition}
    (hSeq : FiringSequence N M ts M') (K : N.Marking) :
    FiringSequence N (M + K) ts (M' + K) := by
  induction hSeq with
  | nil M =>
      exact FiringSequence.nil (M + K)
  | cons hEnabled hTail ih =>
      exact FiringSequence.cons
        (enabled_add_right K hEnabled)
        (by
          simpa [fire_add_right_of_enabled K hEnabled] using ih)

end FiringSequence

namespace Reachable

theorem add_right
    {N : Net} {M M' : N.Marking}
    (hReach : Reachable N M M') (K : N.Marking) :
    Reachable N (M + K) (M' + K) := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
  exact Reachable.of_firingSequence (FiringSequence.add_right hSeq K)

end Reachable

end Petri
end Pm4Lean
