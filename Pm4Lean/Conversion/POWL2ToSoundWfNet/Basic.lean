import Pm4Lean.Conversion.Basic
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target

namespace Pm4Lean
namespace ProcessModel

/--
A POWL2 conversion package: the map into labeled WF-nets, semantic/language
preservation, and soundness of each generated target.
-/
structure SoundPOWL2ToLabeledWFNetConversion (Activity : Type u) where
  conversion : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)
  preserves_semantics :
    ∀ p, Language.Equivalent (POWL2.language p)
      (Petri.LabeledWFNet.language (conversion.map p))
  preserves_language :
    PreservesLanguage POWL2.language Petri.LabeledWFNet.language conversion
  sound_target : ∀ p, Petri.Sound (conversion.map p).wfnet

namespace POWL2ToSoundWfNet

variable {Activity : Type u}

/-- The POWL2-to-labeled-WF-net conversion map. -/
def conversion :
    Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity) :=
  ⟨target⟩

/-- The bundled sound conversion from POWL2 to labeled workflow nets. -/
def soundConversion :
    SoundPOWL2ToLabeledWFNetConversion Activity where
  conversion := conversion
  preserves_semantics := preserves_language
  preserves_language := preserves_language
  sound_target := sound_target

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
