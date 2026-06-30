import Pm4Lean.Models.Petri.WFNet.Behavior.EasySoundness

namespace Pm4Lean
namespace Petri

/--
Each transition occurs in at least one execution that can still complete.
Easy soundness is included so empty-transition nets have a direct sanity
condition instead of making implications depend on inhabited transitions.
-/
def RelaxedSoundness (W : WFNet) : Prop :=
  EasySoundness W ∧
    ∀ t : W.net.Transition, ∃ M₁ M₂ : W.Marking,
      Reachable W.net W.initial M₁ ∧
      Enabled W.net M₁ t ∧
      Step W.net M₁ M₂ ∧
      Reachable W.net M₂ W.final

theorem relaxed_soundness_implies_easy_soundness {W : WFNet}
    (h : RelaxedSoundness W) : EasySoundness W :=
  h.1

end Petri
end Pm4Lean
