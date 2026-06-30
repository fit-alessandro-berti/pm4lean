import Pm4Lean.Models.Language

namespace Pm4Lean
namespace ProcessModel

/-- A conversion between two model families. -/
structure Conversion (Source : Type u) (Target : Type v) where
  map : Source → Target

/-- A conversion preserves denotational trace languages. -/
def PreservesLanguage {Source : Type u} {Target : Type v} {Activity : Type w}
    (sourceLanguage : Source → Language Activity)
    (targetLanguage : Target → Language Activity)
    (C : Conversion Source Target) : Prop :=
  ∀ s, Language.Equivalent (sourceLanguage s) (targetLanguage (C.map s))

theorem preserves_language_refl {Source : Type u} {Activity : Type v}
    (language : Source → Language Activity) :
    PreservesLanguage language language ⟨id⟩ :=
  fun s => Language.equivalent_refl (language s)

end ProcessModel
end Pm4Lean
