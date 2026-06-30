import Pm4Lean.Models.Petri.Semantics.Step

namespace Pm4Lean
namespace Petri

/-- Firing a concrete list of transitions from a marking to a marking. -/
inductive FiringSequence (N : Net) : N.Marking → List N.Transition → N.Marking → Prop where
  | nil (M : N.Marking) : FiringSequence N M [] M
  | cons {M M'' : N.Marking} {t : N.Transition} {ts : List N.Transition} :
      Enabled N M t →
      FiringSequence N (fire N M t) ts M'' →
      FiringSequence N M (t :: ts) M''

namespace FiringSequence

theorem append {N : Net} {M M' M'' : N.Marking}
    {xs ys : List N.Transition}
    (hxs : FiringSequence N M xs M') (hys : FiringSequence N M' ys M'') :
    FiringSequence N M (xs ++ ys) M'' := by
  induction hxs with
  | nil M =>
      simpa using hys
  | cons hEnabled hTail ih =>
      simp
      exact FiringSequence.cons hEnabled (ih hys)

end FiringSequence
end Petri
end Pm4Lean
