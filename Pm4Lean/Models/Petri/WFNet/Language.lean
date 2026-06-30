import Pm4Lean.Models.Petri.WFNet.InitialFinalMarking
import Pm4Lean.Models.Petri.Semantics.FiringSequence
import Pm4Lean.Models.Language

namespace Pm4Lean
namespace Petri

/-- A WF-net together with visible labels for its transitions. -/
structure LabeledWFNet (Activity : Type u) where
  wfnet : WFNet
  label : wfnet.net.Transition → Option Activity

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

/-- A labeled WF-net accepts traces from its initial to final marking. -/
def language (LW : LabeledWFNet Activity) : ProcessModel.Language Activity :=
  fun σ => ∃ ts : List LW.wfnet.net.Transition,
    FiringSequence LW.wfnet.net LW.wfnet.initial ts LW.wfnet.final ∧
    traceOf LW ts = σ

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

theorem language_of_firingSequence
    (LW : LabeledWFNet Activity)
    {ts : List LW.wfnet.net.Transition}
    (hSeq : FiringSequence LW.wfnet.net LW.wfnet.initial ts LW.wfnet.final) :
    language LW (traceOf LW ts) :=
  ⟨ts, hSeq, rfl⟩

theorem empty_trace_of_initial_final
    (LW : LabeledWFNet Activity) (h : LW.wfnet.initial = LW.wfnet.final) :
    language LW [] := by
  refine ⟨[], ?_, rfl⟩
  rw [h]
  exact FiringSequence.nil LW.wfnet.final

/-- Places of a one-transition workflow net. -/
inductive SingleTransitionPlace where
  | initial
  | final
deriving DecidableEq, Repr

/-- The only transition of a one-transition workflow net. -/
inductive SingleTransition where
  | task
deriving DecidableEq, Repr

namespace SingleTransitionExample

/-- A WF-net with one transition moving one token from `initial` to `final`. -/
def wfnet : WFNet where
  net := {
    Place := SingleTransitionPlace
    Transition := SingleTransition
    placeDecEq := inferInstance
    transitionDecEq := inferInstance
    places := [SingleTransitionPlace.initial, SingleTransitionPlace.final]
    transitions := [SingleTransition.task]
    places_complete := by
      intro p
      cases p <;> simp
    transitions_complete := by
      intro t
      cases t
      simp
    pre := fun
      | SingleTransition.task =>
          Marking.singleton SingleTransitionPlace.initial
    post := fun
      | SingleTransition.task =>
          Marking.singleton SingleTransitionPlace.final
  }
  i := SingleTransitionPlace.initial
  o := SingleTransitionPlace.final

/-- The one-transition WF-net labeled by a visible activity. -/
def labeled (a : Activity) : LabeledWFNet Activity where
  wfnet := wfnet
  label := fun
    | SingleTransition.task => some a

theorem task_enabled :
    Enabled wfnet.net wfnet.initial SingleTransition.task := by
  intro p
  cases p <;> simp [wfnet, WFNet.initial, Marking.singleton]

theorem fire_task :
    fire wfnet.net wfnet.initial SingleTransition.task = wfnet.final := by
  apply Marking.ext
  intro p
  cases p <;> native_decide

theorem firing_sequence_task :
    FiringSequence wfnet.net wfnet.initial
      [SingleTransition.task] wfnet.final := by
  apply FiringSequence.cons task_enabled
  rw [fire_task]
  exact FiringSequence.nil wfnet.final

theorem traceOf_task (a : Activity) :
    traceOf (labeled a) [SingleTransition.task] = [a] := by
  rfl

theorem language_contains_task (a : Activity) :
    language (labeled a) [a] :=
  ⟨[SingleTransition.task], firing_sequence_task, traceOf_task a⟩

end SingleTransitionExample

end LabeledWFNet
end Petri
end Pm4Lean
