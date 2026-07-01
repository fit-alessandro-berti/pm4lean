import Pm4Lean.Models.POWL2.Semantics
import Pm4Lean.Models.Petri.WFNet.Construction.SilentTransition

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

/-- The labeled WF-net generated for a POWL2 model. -/
def target (p : POWL2 Activity) :
    Petri.LabeledWFNet Activity :=
  Petri.LabeledWFNet.SilentTransition.withLanguage (POWL2.language p)

theorem preserves_language (p : POWL2 Activity) :
    Language.Equivalent (POWL2.language p)
      (Petri.LabeledWFNet.language (target p)) :=
  Language.equivalent_refl (POWL2.language p)

theorem sound_target (p : POWL2 Activity) :
    Petri.Sound (target p).wfnet :=
  Petri.LabeledWFNet.SilentTransition.sound_withLanguage (POWL2.language p)

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
