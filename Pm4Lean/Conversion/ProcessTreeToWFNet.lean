import Pm4Lean.Conversion.ProcessTree
import Pm4Lean.Models.Petri.WFNet.Language
import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace ProcessModel

/--
The proof obligation for any concrete conversion into WF-nets: language
preservation plus the chosen WF-net soundness property for every converted
model.
-/
structure SoundWFNetConversion
    (Source : Type u) (Activity : Type v)
    (sourceLanguage : Source → Language Activity)
    (wfLanguage : Petri.WFNet → Language Activity) where
  conversion : Conversion Source Petri.WFNet
  preserves_language : PreservesLanguage sourceLanguage wfLanguage conversion
  sound_target : ∀ s, Petri.Sound (conversion.map s)

/--
A behavior-preserving conversion from process trees to WF-nets, with classical
soundness required for every generated target.
-/
abbrev SoundProcessTreeToWFNetConversion
    (Activity : Type u)
    (wfLanguage : Petri.WFNet → Language Activity) :=
  SoundWFNetConversion (ProcessTree Activity) Activity
    ProcessTree.language wfLanguage

/--
A conversion into labeled WF-nets should preserve the source trace language and
produce classically sound underlying WF-nets.
-/
structure SoundLabeledWFNetConversion
    (Source : Type u) (Activity : Type v)
    (sourceLanguage : Source → Language Activity) where
  conversion : Conversion Source (Petri.LabeledWFNet Activity)
  preserves_language :
    PreservesLanguage sourceLanguage Petri.LabeledWFNet.language conversion
  sound_target : ∀ s, Petri.Sound (conversion.map s).wfnet

/-- The concrete proof obligation for converting process trees to labeled WF-nets. -/
abbrev SoundProcessTreeToLabeledWFNetConversion (Activity : Type u) :=
  SoundLabeledWFNetConversion (ProcessTree Activity) Activity
    ProcessTree.language

end ProcessModel
end Pm4Lean
