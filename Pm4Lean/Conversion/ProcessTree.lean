import Pm4Lean.Conversion.Basic
import Pm4Lean.Models.ProcessTree.Basic

namespace Pm4Lean
namespace ProcessModel

/-- A conversion from process trees preserves their concrete trace semantics. -/
def PreservesProcessTreeLanguage
    {Activity : Type u} {Target : Type v}
    (targetLanguage : Target → Language Activity)
    (C : Conversion (ProcessTree Activity) Target) : Prop :=
  PreservesLanguage ProcessTree.language targetLanguage C

theorem process_tree_identity_preserves_language {Activity : Type u} :
    PreservesProcessTreeLanguage
      (Activity := Activity) ProcessTree.language ⟨id⟩ :=
  preserves_language_refl ProcessTree.language

end ProcessModel
end Pm4Lean
