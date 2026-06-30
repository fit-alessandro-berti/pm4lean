import Pm4Lean.Conversion.ProcessTreeToWFNet
import Pm4Lean.Models.Petri.WFNet.Examples.SingleTransition

namespace Pm4Lean
namespace ProcessModel

namespace ProcessTreeToWFNet

/-- The atomic process-tree fragment currently supported by the direct WF-net examples. -/
inductive Atomic (Activity : Type u) where
  | tau : Atomic Activity
  | activity : Activity → Atomic Activity
deriving Repr

namespace Atomic

variable {Activity : Type u}

/-- Embed the atomic fragment into ordinary process-tree syntax. -/
def toProcessTree : Atomic Activity → ProcessTree Activity
  | tau => ProcessTree.tau
  | activity a => ProcessTree.activity a

/-- The process-tree language of an atomic tree. -/
def language (A : Atomic Activity) : Language Activity :=
  ProcessTree.language A.toProcessTree

/-- Translate the activity fragment into the one-transition labeled WF-net. -/
def activityTarget (a : Activity) : Petri.LabeledWFNet Activity :=
  Petri.LabeledWFNet.SingleTransitionExample.labeled a

theorem activity_forward_language
    (a : Activity) :
    Language.Subset
      (language (activity a))
      (Petri.LabeledWFNet.language (activityTarget a)) := by
  intro σ hσ
  simp [language, toProcessTree, ProcessTree.language] at hσ
  rw [hσ]
  exact Petri.LabeledWFNet.SingleTransitionExample.language_contains_task a

theorem activity_preserves_language
    (a : Activity) :
    Language.Equivalent
      (language (activity a))
      (Petri.LabeledWFNet.language (activityTarget a)) := by
  have hSource :
      Language.Equivalent (language (activity a)) (Language.singleton a) := by
    simpa [language, toProcessTree, ProcessTree.language] using
      (Language.equivalent_refl (Language.singleton a))
  exact Language.equivalent_trans hSource
    (Language.equivalent_symm
      (Petri.LabeledWFNet.SingleTransitionExample.language_equiv_singleton a))

end Atomic
end ProcessTreeToWFNet
end ProcessModel
end Pm4Lean
