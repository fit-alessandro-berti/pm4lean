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

end POWL
end ProcessModel
end Pm4Lean
