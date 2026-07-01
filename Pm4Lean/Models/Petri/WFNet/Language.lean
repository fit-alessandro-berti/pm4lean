import Pm4Lean.Models.Petri.WFNet.InitialFinalMarking
import Pm4Lean.Models.Petri.Semantics.FiringSequence
import Pm4Lean.Models.Language

namespace Pm4Lean
namespace Petri

/-- A WF-net together with visible labels for its transitions. -/
structure LabeledWFNet (Activity : Type u) where
  wfnet : WFNet
  label : wfnet.net.Transition → Option Activity
  accepted : ProcessModel.Language Activity

namespace LabeledWFNet

variable {Activity : Type u}

abbrev Marking (LW : LabeledWFNet Activity) := LW.wfnet.Marking

/-- The visible trace emitted by a concrete transition sequence. -/
def traceOf (LW : LabeledWFNet Activity) :
    List LW.wfnet.net.Transition → ProcessModel.Trace Activity
  | [] => []
  | t :: ts =>
      match LW.label t with
      | none => traceOf LW ts
      | some a => a :: traceOf LW ts

/-- The operational firing-sequence language of a labeled WF-net. -/
def operationalLanguage (LW : LabeledWFNet Activity) : ProcessModel.Language Activity :=
  fun σ => ∃ ts : List LW.wfnet.net.Transition,
    FiringSequence LW.wfnet.net LW.wfnet.initial ts LW.wfnet.final ∧
    traceOf LW ts = σ

/-- The accepted trace language carried by a labeled WF-net. -/
def language (LW : LabeledWFNet Activity) : ProcessModel.Language Activity :=
  LW.accepted

theorem traceOf_nil (LW : LabeledWFNet Activity) :
    traceOf LW [] = [] :=
  rfl

theorem traceOf_cons_silent
    (LW : LabeledWFNet Activity) (t : LW.wfnet.net.Transition)
    (ts : List LW.wfnet.net.Transition) (h : LW.label t = none) :
    traceOf LW (t :: ts) = traceOf LW ts := by
  simp [traceOf, h]

theorem traceOf_cons_visible
    (LW : LabeledWFNet Activity) (t : LW.wfnet.net.Transition)
    (ts : List LW.wfnet.net.Transition) (a : Activity)
    (h : LW.label t = some a) :
    traceOf LW (t :: ts) = a :: traceOf LW ts := by
  simp [traceOf, h]

theorem traceOf_map
    (source target : LabeledWFNet Activity)
    (mapTransition :
      source.wfnet.net.Transition → target.wfnet.net.Transition)
    (hLabel :
      ∀ t, target.label (mapTransition t) = source.label t)
    (ts : List source.wfnet.net.Transition) :
    traceOf target (ts.map mapTransition) = traceOf source ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp [traceOf, hLabel t, ih]

theorem traceOf_append
    (LW : LabeledWFNet Activity)
    (xs ys : List LW.wfnet.net.Transition) :
    traceOf LW (xs ++ ys) = traceOf LW xs ++ traceOf LW ys := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
      cases h : LW.label t <;> simp [traceOf, h, ih]

theorem language_of_firingSequence
    (LW : LabeledWFNet Activity)
    {ts : List LW.wfnet.net.Transition}
    (hSeq : FiringSequence LW.wfnet.net LW.wfnet.initial ts LW.wfnet.final) :
    operationalLanguage LW (traceOf LW ts) :=
  ⟨ts, hSeq, rfl⟩

theorem operationalLanguage.exists_firingSequence
    (LW : LabeledWFNet Activity) {σ : ProcessModel.Trace Activity}
    (h : operationalLanguage LW σ) :
    ∃ ts : List LW.wfnet.net.Transition,
      FiringSequence LW.wfnet.net LW.wfnet.initial ts LW.wfnet.final ∧
      traceOf LW ts = σ :=
  h

theorem language_of_firingSequence_append
    (LW : LabeledWFNet Activity)
    {M : LW.wfnet.net.Marking}
    {xs ys : List LW.wfnet.net.Transition}
    (hxs : FiringSequence LW.wfnet.net LW.wfnet.initial xs M)
    (hys : FiringSequence LW.wfnet.net M ys LW.wfnet.final) :
    operationalLanguage LW (traceOf LW xs ++ traceOf LW ys) := by
  refine ⟨xs ++ ys, FiringSequence.append hxs hys, ?_⟩
  exact traceOf_append LW xs ys

theorem firingSequence_append_trace
    (LW : LabeledWFNet Activity)
    {M : LW.wfnet.net.Marking}
    {xs ys : List LW.wfnet.net.Transition}
    {σ τ : ProcessModel.Trace Activity}
    (hxs : FiringSequence LW.wfnet.net LW.wfnet.initial xs M)
    (hys : FiringSequence LW.wfnet.net M ys LW.wfnet.final)
    (hσ : traceOf LW xs = σ) (hτ : traceOf LW ys = τ) :
    operationalLanguage LW (σ ++ τ) := by
  refine ⟨xs ++ ys, FiringSequence.append hxs hys, ?_⟩
  rw [traceOf_append, hσ, hτ]

theorem operationalLanguage_of_map
    (source target : LabeledWFNet Activity)
    (mapMarking :
      source.wfnet.net.Marking → target.wfnet.net.Marking)
    (mapTransition :
      source.wfnet.net.Transition → target.wfnet.net.Transition)
    (hInitial : mapMarking source.wfnet.initial = target.wfnet.initial)
    (hFinal : mapMarking source.wfnet.final = target.wfnet.final)
    (hEnabled :
      ∀ {M : source.wfnet.net.Marking}
        {t : source.wfnet.net.Transition},
        Enabled source.wfnet.net M t →
          Enabled target.wfnet.net (mapMarking M) (mapTransition t))
    (hFire :
      ∀ (M : source.wfnet.net.Marking)
        (t : source.wfnet.net.Transition),
        mapMarking (fire source.wfnet.net M t) =
          fire target.wfnet.net (mapMarking M) (mapTransition t))
    (hLabel :
      ∀ t, target.label (mapTransition t) = source.label t)
    {σ : ProcessModel.Trace Activity}
    (h : operationalLanguage source σ) :
    operationalLanguage target σ := by
  rcases h with ⟨ts, hSeq, hTrace⟩
  refine ⟨ts.map mapTransition, ?_, ?_⟩
  · rw [← hInitial, ← hFinal]
    exact FiringSequence.map mapMarking mapTransition hEnabled hFire hSeq
  · rw [traceOf_map source target mapTransition hLabel ts]
    exact hTrace

theorem empty_trace_of_initial_final
    (LW : LabeledWFNet Activity) (h : LW.wfnet.initial = LW.wfnet.final) :
    operationalLanguage LW [] := by
  refine ⟨[], ?_, rfl⟩
  rw [h]
  exact FiringSequence.nil LW.wfnet.final

end LabeledWFNet
end Petri
end Pm4Lean
