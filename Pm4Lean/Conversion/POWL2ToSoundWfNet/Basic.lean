import Pm4Lean.Conversion.Basic
import Pm4Lean.Conversion.POWL2ToSoundWfNet.Target
import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace ProcessModel

/--
The semantic correctness property still required for a complete POWL2-to-WF-net
conversion: every trace denoted by the POWL2 model is produced by a concrete
Petri firing sequence in the generated net.
-/
def POWL2LanguageRealizedByFiring
    {Activity : Type u}
    (C : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)) : Prop :=
  ∀ p {σ : Trace Activity},
    POWL2.language p σ →
      ∃ ts : List (C.map p).wfnet.net.Transition,
        Petri.FiringSequence (C.map p).wfnet.net
          (C.map p).wfnet.initial ts (C.map p).wfnet.final ∧
        Petri.LabeledWFNet.traceOf (C.map p) ts = σ

/-- Every generated target WF-net is behaviorally sound. -/
def POWL2TargetsSound
    {Activity : Type u}
    (C : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)) : Prop :=
  ∀ p, Petri.Sound (C.map p).wfnet

/-- Every generated target is a classical sound WF-net. -/
def POWL2TargetsClassicallySound
    {Activity : Type u}
    (C : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)) : Prop :=
  ∀ p, Petri.ClassicalSoundness (C.map p).wfnet

theorem POWL2LanguageRealizedByFiring.of_operational
    {Activity : Type u}
    {C : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)}
    (hOperational :
      ∀ p {σ : Trace Activity},
        POWL2.language p σ →
          Petri.LabeledWFNet.operationalLanguage (C.map p) σ) :
    POWL2LanguageRealizedByFiring C := by
  intro p σ h
  simpa [Petri.LabeledWFNet.operationalLanguage] using hOperational p h

theorem POWL2LanguageRealizedByFiring.of_accepted_subset
    {Activity : Type u}
    {C : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)}
    (hAcceptedRealized :
      ∀ p {σ : Trace Activity},
        Petri.LabeledWFNet.language (C.map p) σ →
          ∃ ts : List (C.map p).wfnet.net.Transition,
            Petri.FiringSequence (C.map p).wfnet.net
              (C.map p).wfnet.initial ts (C.map p).wfnet.final ∧
            Petri.LabeledWFNet.traceOf (C.map p) ts = σ)
    (hSubset :
      ∀ p, Language.Subset (POWL2.language p)
        (Petri.LabeledWFNet.language (C.map p))) :
    POWL2LanguageRealizedByFiring C := by
  intro p σ h
  exact hAcceptedRealized p (hSubset p σ h)

/-- A POWL2 conversion package whose target language is Petri firing behavior. -/
structure POWL2ToLabeledWFNetConversion (Activity : Type u) where
  conversion : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)
  language_eq_operational :
    ∀ p, Petri.LabeledWFNet.language (conversion.map p) =
      Petri.LabeledWFNet.operationalLanguage (conversion.map p)
  accepted_language_realized_by_firing :
    ∀ p {σ : Trace Activity},
      Petri.LabeledWFNet.language (conversion.map p) σ →
        ∃ ts : List (conversion.map p).wfnet.net.Transition,
          Petri.FiringSequence (conversion.map p).wfnet.net
            (conversion.map p).wfnet.initial ts (conversion.map p).wfnet.final ∧
          Petri.LabeledWFNet.traceOf (conversion.map p) ts = σ

/--
The final conversion contract: POWL2 source traces are realized by concrete
Petri firing sequences, and all generated workflow nets are sound.
-/
structure CompletePOWL2ToSoundWFNetConversion (Activity : Type u) where
  conversion : Conversion (POWL2 Activity) (Petri.LabeledWFNet Activity)
  source_language_realized_by_firing :
    POWL2LanguageRealizedByFiring conversion
  targets_sound : POWL2TargetsSound conversion

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
  accepted_language_realized_by_firing := accepted_language_realized_by_firing

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
