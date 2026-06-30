import Pm4Lean.Models.Petri.WFNet.Behavior.OptionToComplete

namespace Pm4Lean
namespace Petri

/-- Every transition can be enabled in at least one reachable marking. -/
def NoDeadTransitions (W : WFNet) : Prop :=
  ∀ t : W.net.Transition, ∃ M : W.Marking,
    Reachable W.net W.initial M ∧ Enabled W.net M t

/-- A transition is enabled after executing a concrete transition sequence. -/
def TransitionEnabledAfterSequence
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition)
    (t : N.Transition) : Prop :=
  ∃ M : N.Marking, FiringSequence N M₀ ts M ∧ Enabled N M t

/-- A transition with no reachable enabling marking. -/
def DeadTransition (W : WFNet) (t : W.net.Transition) : Prop :=
  ¬ ∃ M : W.Marking, Reachable W.net W.initial M ∧ Enabled W.net M t

theorem no_dead_transitions_iff_enabled_after_sequence (W : WFNet) :
    NoDeadTransitions W ↔
      ∀ t : W.net.Transition, ∃ ts : List W.net.Transition,
        TransitionEnabledAfterSequence W.net W.initial ts t := by
  constructor
  · intro hNoDead t
    obtain ⟨M, hReach, hEnabled⟩ := hNoDead t
    obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
    exact ⟨ts, M, hSeq, hEnabled⟩
  · intro hSeq t
    obtain ⟨ts, M, hFiring, hEnabled⟩ := hSeq t
    exact ⟨M, Reachable.of_firingSequence hFiring, hEnabled⟩

end Petri
end Pm4Lean
