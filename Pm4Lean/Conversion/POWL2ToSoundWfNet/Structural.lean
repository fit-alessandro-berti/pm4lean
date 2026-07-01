import Pm4Lean.Conversion.POWL2ToSoundWfNet.Structural.Arcs

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace Structural

/-- Raw finite Petri data generated from a POWL2 model. -/
structure RawNet (Activity : Type u) where
  places : List RawPlace
  transitions : List RawTransition
  pre : RawTransition → RawPlace → Nat
  post : RawTransition → RawPlace → Nat
  label : RawTransition → Option Activity
  source : RawPlace
  sink : RawPlace

/--
The structural compiler produces the concrete places, transitions, arcs, and
labels for every native POWL2 construct.  The proof-oriented wrapper into
`Petri.Net` is kept separate because it needs finite-subtype membership lemmas.
-/
noncomputable def rawNet (p : POWL2 Activity) : RawNet Activity where
  places := rawPlacesRoot p
  transitions := rawTransitionsRoot p
  pre := rawPre (compiled p)
  post := rawPost (compiled p)
  label := rawLabel (compiled p)
  source := entry []
  sink := exit []

abbrev Place (p : POWL2 Activity) := { q : RawPlace // q ∈ rawPlacesRoot p }
abbrev Transition (p : POWL2 Activity) :=
  { t : RawTransition // t ∈ rawTransitionsRoot p }

theorem raw_source_mem (p : POWL2 Activity) :
    entry [] ∈ rawPlaces p [] := by
  cases p <;> simp [rawPlaces, entry, placesForPartialOrder]

theorem raw_sink_mem (p : POWL2 Activity) :
    exit [] ∈ rawPlaces p [] := by
  cases p <;> simp [rawPlaces, exit, placesForPartialOrder]

theorem source_mem (p : POWL2 Activity) :
    entry [] ∈ rawPlacesRoot p :=
  raw_source_mem (compiled p)

theorem sink_mem (p : POWL2 Activity) :
    exit [] ∈ rawPlacesRoot p :=
  raw_sink_mem (compiled p)

noncomputable def net (p : POWL2 Activity) : Petri.Net where
  Place := Place p
  Transition := Transition p
  placeDecEq := inferInstance
  transitionDecEq := inferInstance
  places := (rawPlacesRoot p).attach
  transitions := (rawTransitionsRoot p).attach
  places_complete := by
    intro q
    exact List.mem_attach _ _
  transitions_complete := by
    intro t
    exact List.mem_attach _ _
  pre := fun t q => rawPre (compiled p) t.1 q.1
  post := fun t q => rawPost (compiled p) t.1 q.1

noncomputable def wfnet (p : POWL2 Activity) : Petri.WFNet where
  net := net p
  i := ⟨entry [], source_mem p⟩
  o := ⟨exit [], sink_mem p⟩

/--
Generic structural conversion.  The accepted language is the operational firing
language of the generated net; it is not copied from the POWL2 denotation.
-/
noncomputable def target (p : POWL2 Activity) :
    Petri.LabeledWFNet Activity where
  wfnet := wfnet p
  label := fun t => rawLabel (compiled p) t.1
  accepted := fun σ =>
    ∃ ts : List (wfnet p).net.Transition,
      Petri.FiringSequence (wfnet p).net (wfnet p).initial ts (wfnet p).final ∧
      Petri.LabeledWFNet.traceOf
        { wfnet := wfnet p, label := fun t => rawLabel (compiled p) t.1,
          accepted := fun _ => False } ts = σ

theorem traceOf_eq_of_same_label
    (W : Petri.WFNet) (label : W.net.Transition → Option Activity)
    (accepted₁ accepted₂ : Language Activity)
    (ts : List W.net.Transition) :
    Petri.LabeledWFNet.traceOf
        { wfnet := W, label := label, accepted := accepted₁ } ts =
      Petri.LabeledWFNet.traceOf
        { wfnet := W, label := label, accepted := accepted₂ } ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      cases label t <;> simp [Petri.LabeledWFNet.traceOf, ih]

theorem language_eq_operational (p : POWL2 Activity) :
    Petri.LabeledWFNet.language (target p) =
      Petri.LabeledWFNet.operationalLanguage (target p) := by
  funext σ
  apply propext
  constructor
  · intro h
    rcases h with ⟨ts, hSeq, hTrace⟩
    refine ⟨ts, hSeq, ?_⟩
    have hEq :
        Petri.LabeledWFNet.traceOf
          { wfnet := wfnet p, label := fun t => rawLabel (compiled p) t.1,
            accepted := fun _ => False } ts =
        Petri.LabeledWFNet.traceOf (target p) ts := by
      simpa [target] using
        traceOf_eq_of_same_label
          (W := wfnet p) (label := fun t => rawLabel (compiled p) t.1)
          (accepted₁ := fun _ => False)
          (accepted₂ := (target p).accepted) ts
    exact hEq.symm.trans hTrace
  · intro h
    rcases h with ⟨ts, hSeq, hTrace⟩
    refine ⟨ts, hSeq, ?_⟩
    have hEq :
        Petri.LabeledWFNet.traceOf
          { wfnet := wfnet p, label := fun t => rawLabel (compiled p) t.1,
            accepted := fun _ => False } ts =
        Petri.LabeledWFNet.traceOf (target p) ts := by
      simpa [target] using
        traceOf_eq_of_same_label
          (W := wfnet p) (label := fun t => rawLabel (compiled p) t.1)
          (accepted₁ := fun _ => False)
          (accepted₂ := (target p).accepted) ts
    exact hEq.trans hTrace

theorem language_realized_by_firing
    (p : POWL2 Activity) {σ : Trace Activity}
    (h : Petri.LabeledWFNet.language (target p) σ) :
    ∃ ts : List (target p).wfnet.net.Transition,
      Petri.FiringSequence (target p).wfnet.net
        (target p).wfnet.initial ts (target p).wfnet.final ∧
      Petri.LabeledWFNet.traceOf (target p) ts = σ := by
  simpa [Petri.LabeledWFNet.operationalLanguage]
    using (show Petri.LabeledWFNet.operationalLanguage (target p) σ from
      by
        rw [← language_eq_operational p]
        exact h)

end Structural

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
