import Pm4Lean.Models.Petri.Semantics.FiringSequence

namespace Pm4Lean
namespace Petri

/-- Reachability is the reflexive-transitive closure of one-step firing. -/
inductive Reachable (N : Net) : N.Marking → N.Marking → Prop where
  | refl (M : N.Marking) : Reachable N M M
  | step {M M' M'' : N.Marking} :
      Step N M M' → Reachable N M' M'' → Reachable N M M''

namespace Reachable

theorem trans {N : Net} {M M' M'' : N.Marking}
    (h₁ : Reachable N M M') (h₂ : Reachable N M' M'') :
    Reachable N M M'' := by
  induction h₁ with
  | refl M =>
      exact h₂
  | step hStep hReach ih =>
      exact Reachable.step hStep (ih h₂)

theorem of_step {N : Net} {M M' : N.Marking} (h : Step N M M') :
    Reachable N M M' :=
  Reachable.step h (Reachable.refl M')

theorem of_enabled {N : Net} {M : N.Marking} {t : N.Transition}
    (h : Enabled N M t) :
    Reachable N M (fire N M t) :=
  of_step (Step.fire h)

theorem of_firingSequence {N : Net} {M M' : N.Marking}
    {ts : List N.Transition} (h : FiringSequence N M ts M') :
    Reachable N M M' := by
  induction h with
  | nil M =>
      exact Reachable.refl M
  | cons hEnabled hTail ih =>
      exact Reachable.step (Step.fire hEnabled) ih

theorem exists_firingSequence {N : Net} {M M' : N.Marking}
    (h : Reachable N M M') :
    ∃ ts : List N.Transition, FiringSequence N M ts M' := by
  induction h with
  | refl M =>
      exact ⟨[], FiringSequence.nil M⟩
  | step hStep hReach ih =>
      obtain ⟨ts, hSeq⟩ := ih
      cases hStep with
      | fire hEnabled =>
          exact ⟨_ :: ts, FiringSequence.cons hEnabled hSeq⟩

end Reachable
end Petri
end Pm4Lean
