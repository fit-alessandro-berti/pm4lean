import Pm4Lean.Models.Petri.WFNet.Language
import Pm4Lean.Models.Petri.WFNet.Soundness.SoundnessImplications

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
  accepted := ProcessModel.Language.singleton a

/-- The one-transition WF-net with a silent transition. -/
def silent : LabeledWFNet Activity where
  wfnet := wfnet
  label := fun
    | SingleTransition.task => none
  accepted := ProcessModel.Language.epsilon

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
  rfl

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

theorem firing_sequence_from_final_final
    {ts : List SingleTransition} {M : wfnet.Marking}
    (hSeq : FiringSequence wfnet.net wfnet.final ts M) :
    M = wfnet.final := by
  cases hSeq with
  | nil M =>
      rfl
  | cons hEnabled _ =>
      cases task_not_enabled_at_final hEnabled

theorem firing_sequence_from_initial_initial_or_final
    {ts : List SingleTransition} {M : wfnet.Marking}
    (hSeq : FiringSequence wfnet.net wfnet.initial ts M) :
    M = wfnet.initial ∨ M = wfnet.final := by
  cases ts with
  | nil =>
      left
      exact (FiringSequence.eq_of_nil hSeq).symm
  | cons t rest =>
      cases t
      cases hSeq with
      | cons _ hTail =>
          right
          have hTail' : FiringSequence wfnet.net wfnet.final rest M := by
            simpa [fire_task] using hTail
          exact firing_sequence_from_final_final hTail'

theorem reachable_from_initial_initial_or_final
    {M : wfnet.Marking}
    (hReach : Reachable wfnet.net wfnet.initial M) :
    M = wfnet.initial ∨ M = wfnet.final := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
  exact firing_sequence_from_initial_initial_or_final hSeq

theorem reachable_initial_to_final :
    Reachable wfnet.net wfnet.initial wfnet.final :=
  Reachable.of_firingSequence firing_sequence_task

theorem option_to_complete :
    OptionToComplete wfnet := by
  intro M hReach
  cases reachable_from_initial_initial_or_final hReach with
  | inl hInitial =>
      rw [hInitial]
      exact reachable_initial_to_final
  | inr hFinal =>
      rw [hFinal]
      exact Reachable.refl wfnet.final

theorem proper_completion :
    ProperCompletion wfnet := by
  intro M hReach hFinalCovered
  cases reachable_from_initial_initial_or_final hReach with
  | inr hFinal =>
      exact hFinal
  | inl hInitial =>
      exfalso
      have hAtFinal := hFinalCovered SingleTransitionPlace.final
      rw [hInitial] at hAtFinal
      simp [wfnet, WFNet.initial, WFNet.final, Marking.singleton] at hAtFinal

theorem no_dead_transitions :
    NoDeadTransitions wfnet := by
  intro t
  cases t
  exact ⟨wfnet.initial, Reachable.refl wfnet.initial, task_enabled⟩

theorem sound :
    Sound wfnet :=
  sound_of_components option_to_complete proper_completion no_dead_transitions

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
  exact hσ

theorem language_equiv_singleton (a : Activity) :
    ProcessModel.Language.Equivalent
      (language (labeled a)) (ProcessModel.Language.singleton a) := by
  constructor
  · exact language_subset_singleton a
  · intro σ hσ
    exact hσ

end SingleTransitionExample

end LabeledWFNet
end Petri
end Pm4Lean
