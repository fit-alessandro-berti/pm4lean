import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness.ToBehavior.OptionToComplete

namespace Pm4Lean
namespace Petri

theorem live_original_transition_and_proper_completion_implies_not_dead
    {W : WFNet}
    (t : W.net.Transition)
    (hLiveOriginal :
      LiveTransition
        (shortCircuit W)
        W.initial
        (ShortCircuitTransition.original t))
    (hProper : ProperCompletion W) :
    ∃ M : W.Marking, Reachable W.net W.initial M ∧ Enabled W.net M t := by
  obtain ⟨M, hReachShortCircuit, hEnabledShortCircuit⟩ :=
    hLiveOriginal W.initial (Reachable.refl (N := shortCircuit W) W.initial)
  exact ⟨M,
    shortCircuit.reachable_shortCircuit_to_original_of_proper
      W hProper hReachShortCircuit,
    (shortCircuit.original_enabled_iff W M t).1 hEnabledShortCircuit⟩

theorem live_shortCircuit_and_proper_completion_implies_no_dead
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hProper : ProperCompletion W) :
    NoDeadTransitions W := by
  intro t
  exact live_original_transition_and_proper_completion_implies_not_dead
    t (hLive (ShortCircuitTransition.original t)) hProper

end Petri
end Pm4Lean
