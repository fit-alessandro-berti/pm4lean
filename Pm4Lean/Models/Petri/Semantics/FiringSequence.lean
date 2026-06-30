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

theorem eq_of_nil {N : Net} {M M' : N.Marking}
    (h : FiringSequence N M [] M') :
    M = M' := by
  cases h
  rfl

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

theorem split_append {N : Net} {M M'' : N.Marking}
    {xs ys : List N.Transition}
    (h : FiringSequence N M (xs ++ ys) M'') :
    ∃ M' : N.Marking,
      FiringSequence N M xs M' ∧ FiringSequence N M' ys M'' := by
  induction xs generalizing M with
  | nil =>
      exact ⟨M, FiringSequence.nil M, by simpa using h⟩
  | cons t xs ih =>
      cases h with
      | cons hEnabled hTail =>
          obtain ⟨M', hPrefix, hSuffix⟩ := ih hTail
          exact ⟨M',
            FiringSequence.cons hEnabled hPrefix,
            hSuffix⟩

theorem split_append_append {N : Net} {M Mend : N.Marking}
    {xs ys zs : List N.Transition}
    (h : FiringSequence N M ((xs ++ ys) ++ zs) Mend) :
    ∃ Mx My : N.Marking,
      FiringSequence N M xs Mx ∧
        FiringSequence N Mx ys My ∧
          FiringSequence N My zs Mend ∧
            FiringSequence N M (xs ++ ys) My := by
  obtain ⟨My, hPrefixLoop, hSuffix⟩ := split_append h
  obtain ⟨Mx, hPrefix, hLoop⟩ := split_append hPrefixLoop
  exact ⟨Mx, My, hPrefix, hLoop, hSuffix, hPrefixLoop⟩

theorem deterministic {N : Net} {M M₁ M₂ : N.Marking}
    {ts : List N.Transition}
    (h₁ : FiringSequence N M ts M₁)
    (h₂ : FiringSequence N M ts M₂) :
    M₁ = M₂ := by
  induction h₁ generalizing M₂ with
  | nil M =>
      exact eq_of_nil h₂
  | cons hEnabled hTail ih =>
      cases h₂ with
      | cons _ hTail₂ =>
          exact ih hTail₂

end FiringSequence
end Petri
end Pm4Lean
