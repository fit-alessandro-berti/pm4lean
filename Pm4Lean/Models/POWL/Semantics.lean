import Pm4Lean.Models.Language
import Pm4Lean.Models.POWL.Basic

namespace Pm4Lean
namespace ProcessModel
namespace POWL

variable {Activity : Type u}

/--
Concrete finite-trace semantics for POWL terms.

Partial-order nodes use origin-tagged interleavings: every child contributes a
trace, and every event from an ordered predecessor child must occur before every
event from its successor child.
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
  | partialOrder children order =>
      Language.partialOrder (children.map language) order

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
    (show Language.partialOrder ([] : List (Language Activity)) order [] from
      by
        refine ⟨[], [], TracesIn.nil, ?_, ?_, rfl⟩
        · exact IndexedInterleavesFrom.nil 0
        · intro i j _ left₁ a right₁ _ _ _ h _
          cases left₁ <;> simp at h)

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
