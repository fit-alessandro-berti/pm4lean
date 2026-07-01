import Pm4Lean.Models.Petri.WFNet.Examples.SingleTransition

namespace Pm4Lean
namespace Petri
namespace LabeledWFNet
namespace SilentTransition

variable {Activity : Type u}

/-- A reusable silent one-transition labeled WF-net template. -/
def labeled : LabeledWFNet Activity :=
  SingleTransitionExample.silent

/-- Reuse the silent one-transition WF-net with any accepted language. -/
def withLanguage (L : ProcessModel.Language Activity) :
    LabeledWFNet Activity :=
  { labeled with accepted := L }

/-- The silent one-transition template is behaviorally sound. -/
theorem sound :
    Sound (labeled (Activity := Activity)).wfnet :=
  SingleTransitionExample.sound

theorem sound_withLanguage (L : ProcessModel.Language Activity) :
    Sound (withLanguage L).wfnet :=
  SingleTransitionExample.sound

end SilentTransition
end LabeledWFNet
end Petri
end Pm4Lean
