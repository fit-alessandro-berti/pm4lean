import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace Petri

theorem sound_implies_option_to_complete {W : WFNet} (h : Sound W) :
    OptionToComplete W :=
  h.1

theorem sound_implies_proper_completion {W : WFNet} (h : Sound W) :
    ProperCompletion W :=
  h.2.1

theorem sound_implies_no_dead_transitions {W : WFNet} (h : Sound W) :
    NoDeadTransitions W :=
  h.2.2

theorem sound_implies_easy_soundness {W : WFNet} (h : Sound W) :
    EasySoundness W :=
  option_to_complete_implies_easy_soundness h.1

theorem weak_soundness_implies_option_to_complete {W : WFNet}
    (h : WeakSoundness W) : OptionToComplete W :=
  h.1

theorem weak_soundness_implies_proper_completion {W : WFNet}
    (h : WeakSoundness W) : ProperCompletion W :=
  h.2

theorem sound_of_components {W : WFNet}
    (hOption : OptionToComplete W)
    (hProper : ProperCompletion W)
    (hNoDead : NoDeadTransitions W) :
    Sound W :=
  ⟨hOption, hProper, hNoDead⟩

end Petri
end Pm4Lean
