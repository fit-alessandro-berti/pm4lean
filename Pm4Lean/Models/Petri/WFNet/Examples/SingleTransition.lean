import Pm4Lean.Models.Petri.WFNet.Language

namespace Pm4Lean
namespace Petri

namespace LabeledWFNet

variable {Activity : Type u}

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

theorem initial_ne_final : wfnet.initial ≠ wfnet.final := by
  intro h
  have hAtInitial :=
    congrFun h SingleTransitionPlace.initial
  simp [wfnet, WFNet.initial, WFNet.final, Marking.singleton] at hAtInitial

theorem task_not_enabled_at_final :
    ¬ Enabled wfnet.net wfnet.final SingleTransition.task := by
  intro hEnabled
  have hAtInitial := hEnabled SingleTransitionPlace.initial
  simp [wfnet, WFNet.final, Marking.singleton] at hAtInitial

theorem final_to_final_trace_nil
    {ts : List SingleTransition}
    (hSeq : FiringSequence wfnet.net wfnet.final ts wfnet.final)
    (a : Activity) :
    traceOf (labeled a) ts = [] := by
  cases hSeq with
  | nil M =>
      rfl
  | cons hEnabled _ =>
      cases task_not_enabled_at_final hEnabled

theorem initial_to_final_trace_task
    {ts : List SingleTransition}
    (hSeq : FiringSequence wfnet.net wfnet.initial ts wfnet.final)
    (a : Activity) :
    traceOf (labeled a) ts = [a] := by
  cases ts with
  | nil =>
      exact False.elim (initial_ne_final (FiringSequence.eq_of_nil hSeq))
  | cons t rest =>
      cases t
      cases hSeq with
      | cons hEnabled hTail =>
          have hTail' : FiringSequence wfnet.net wfnet.final rest wfnet.final := by
            simpa [fire_task] using hTail
          simp [traceOf, labeled]
          exact final_to_final_trace_nil hTail' a

theorem language_subset_singleton (a : Activity) :
    ProcessModel.Language.Subset
      (language (labeled a)) (ProcessModel.Language.singleton a) := by
  intro σ hσ
  obtain ⟨ts, hSeq, hTrace⟩ := hσ
  rw [← hTrace]
  exact initial_to_final_trace_task hSeq a

theorem language_equiv_singleton (a : Activity) :
    ProcessModel.Language.Equivalent
      (language (labeled a)) (ProcessModel.Language.singleton a) := by
  constructor
  · exact language_subset_singleton a
  · intro σ hσ
    rw [hσ]
    exact language_contains_task a

end SingleTransitionExample

end LabeledWFNet
end Petri
end Pm4Lean
