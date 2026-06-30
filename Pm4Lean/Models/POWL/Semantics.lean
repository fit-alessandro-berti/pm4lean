import Pm4Lean.Models.Language
import Pm4Lean.Models.POWL.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL

variable {Activity : Type u}

/--
Concrete finite-trace semantics for POWL terms.

The current partial-order node semantics interleaves all child languages.  The
order relation is captured by `WellFormed`; order-constrained interleavings can
refine this definition once event-origin tracking is introduced.
-/
noncomputable def language : POWL Activity → Language Activity
  | tau => Language.epsilon
  | activity a => Language.singleton a
  | xor l r => Language.union (language l) (language r)
  | loop body redo =>
      Language.seq (language body)
        (Language.Star (Language.seq (language redo) (language body)))
  | partialOrder [l, r] order =>
      by
        classical
        exact
          if order 0 1 then
            Language.seq (language l) (language r)
          else if order 1 0 then
            Language.seq (language r) (language l)
          else
            Language.parallel (language l) (language r)
  | partialOrder children _ =>
      Language.interleaving (children.map language)

theorem tau_language :
    language (Activity := Activity) tau = Language.epsilon :=
  by simp [language]

theorem activity_language (a : Activity) :
    language (activity a) = Language.singleton a :=
  by simp [language]

theorem xor_language (l r : POWL Activity) :
    language (xor l r) = Language.union (language l) (language r) :=
  by simp [language]

theorem loop_body_once {body redo : POWL Activity} {σ : Trace Activity}
    (hBody : language body σ) :
    language (loop body redo) σ := by
  simp [language]
  exact ⟨σ, [], hBody, Language.Star.nil, by simp⟩

theorem partialOrder_nil_language (order : Nat → Nat → Prop) :
    language (partialOrder ([] : List (POWL Activity)) order) [] := by
  simpa [language] using
    (Language.interleaving_nil (Activity := Activity))

theorem partialOrder_singleton_equiv
    (child : POWL Activity) (order : Nat → Nat → Prop) :
    Language.Equivalent
      (language (partialOrder [child] order))
      (language child) := by
  simpa [language] using
    (Language.interleaving_singleton (language child))

theorem partialOrder_pair_sequence_language
    (l r : POWL Activity) :
    language (partialOrder [l, r] (fun i j => i = 0 ∧ j = 1)) =
      Language.seq (language l) (language r) := by
  classical
  simp [language]

theorem partialOrder_pair_parallel_language
    (l r : POWL Activity) :
    language (partialOrder [l, r] (fun _ _ => False)) =
      Language.parallel (language l) (language r) := by
  classical
  simp [language]

end POWL
end ProcessModel
end Pm4Lean
