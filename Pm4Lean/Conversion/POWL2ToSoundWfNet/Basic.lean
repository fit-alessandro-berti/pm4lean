import Pm4Lean.Conversion.Basic
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target

namespace Pm4Lean
namespace ProcessModel

/-- A POWL2 conversion package whose target language is Petri firing behavior. -/
structure POWL2ToLabeledWFNetConversion (Activity : Type u) where
  conversion : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)
  language_eq_operational :
    ∀ p, Petri.LabeledWFNet.language (conversion.map p) =
      Petri.LabeledWFNet.operationalLanguage (conversion.map p)
  language_realized_by_firing :
    ∀ p {σ : Trace Activity},
      Petri.LabeledWFNet.language (conversion.map p) σ →
        ∃ ts : List (conversion.map p).wfnet.net.Transition,
          Petri.FiringSequence (conversion.map p).wfnet.net
            (conversion.map p).wfnet.initial ts (conversion.map p).wfnet.final ∧
          Petri.LabeledWFNet.traceOf (conversion.map p) ts = σ

namespace POWL2ToSoundWfNet

variable {Activity : Type u}

/-- The POWL2-to-labeled-WF-net conversion map. -/
noncomputable def conversion :
    Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity) :=
  ⟨target⟩

/-- The bundled structural conversion from POWL2 to labeled workflow nets. -/
noncomputable def structuralConversion :
    POWL2ToLabeledWFNetConversion Activity where
  conversion := conversion
  language_eq_operational := language_eq_operational
  language_realized_by_firing := language_realized_by_firing

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
