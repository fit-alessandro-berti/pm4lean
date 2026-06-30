import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness.ToBehavior

namespace Pm4Lean
namespace Petri

theorem original_transition_live_of_cycle_and_no_dead
    {W : WFNet}
    (hCycle :
      ∀ M : W.Marking, Reachable (shortCircuit W) W.initial M →
        Reachable (shortCircuit W) M W.initial)
    (hNoDead : NoDeadTransitions W)
    (t : W.net.Transition) :
    LiveTransition
      (shortCircuit W)
      W.initial
      (ShortCircuitTransition.original t) := by
  intro M hReach
  have hToInitial : Reachable (shortCircuit W) M W.initial :=
    hCycle M hReach
  obtain ⟨MEnable, hReachOriginal, hEnabled⟩ := hNoDead t
  have hReachEnableShortCircuit :
      Reachable (shortCircuit W) W.initial MEnable :=
    shortCircuit.reachable_original_to_shortCircuit W hReachOriginal
  exact ⟨MEnable,
    Reachable.trans hToInitial hReachEnableShortCircuit,
    (shortCircuit.original_enabled_iff W MEnable t).2 hEnabled⟩

theorem live_of_cycle_and_sound
    {W : WFNet}
    (hCycle :
      ∀ M : W.Marking, Reachable (shortCircuit W) W.initial M →
        Reachable (shortCircuit W) M W.initial)
    (hSound : Sound W) :
    Live (shortCircuit W) W.initial := by
  intro t
  cases t with
  | inl t =>
      exact original_transition_live_of_cycle_and_no_dead
        hCycle hSound.2.2 t
  | inr u =>
      cases u
      exact return_transition_live_of_cycle hCycle hSound.1

theorem live_of_sound
    {W : WFNet}
    (hSound : Sound W) :
  Live (shortCircuit W) W.initial :=
  live_of_cycle_and_sound
    (fun _M hReach =>
      shortCircuit_reaches_initial_from_reachable
        hSound.1 hSound.2.1 hReach)
    hSound

end Petri
end Pm4Lean
