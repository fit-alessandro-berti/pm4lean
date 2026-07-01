import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

/-- The labeled WF-net generated structurally from a POWL2 model. -/
noncomputable def target (p : POWL2 Activity) :
    Petri.LabeledWFNet Activity :=
  Structural.target p

theorem language_eq_operational (p : POWL2 Activity) :
    Petri.LabeledWFNet.language (target p) =
      Petri.LabeledWFNet.operationalLanguage (target p) :=
  Structural.language_eq_operational p

theorem language_realized_by_firing
    (p : POWL2 Activity) {σ : Trace Activity}
    (h : Petri.LabeledWFNet.language (target p) σ) :
    ∃ ts : List (target p).wfnet.net.Transition,
      Petri.FiringSequence (target p).wfnet.net
        (target p).wfnet.initial ts (target p).wfnet.final ∧
      Petri.LabeledWFNet.traceOf (target p) ts = σ := by
  exact Structural.language_realized_by_firing p h

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
