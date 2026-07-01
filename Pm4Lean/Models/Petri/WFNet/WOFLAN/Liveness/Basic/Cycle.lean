import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness.Basic.Original

namespace Pm4Lean
namespace Petri

theorem shortCircuit_reaches_initial_from_reachable
    {W : WFNet}
    (hOption : OptionToComplete W)
    (hProper : ProperCompletion W)
    {M : W.Marking}
    (hReachSC : Reachable (shortCircuit W) W.initial M) :
    Reachable (shortCircuit W) M W.initial := by
  have hReachOriginal : Reachable W.net W.initial M :=
    shortCircuit.reachable_shortCircuit_to_original_of_proper
      W hProper hReachSC
  have hReachFinalOriginal : Reachable W.net M W.final :=
    hOption M hReachOriginal
  have hReachFinalShortCircuit :
      Reachable (shortCircuit W) M W.final :=
    shortCircuit.reachable_original_to_shortCircuit W hReachFinalOriginal
  exact Reachable.trans hReachFinalShortCircuit
    (shortCircuit.reachable_final_to_initial_in_shortCircuit W)

theorem return_transition_live_of_cycle
    {W : WFNet}
    (hCycle :
      ∀ M : W.Marking, Reachable (shortCircuit W) W.initial M →
        Reachable (shortCircuit W) M W.initial)
    (hOption : OptionToComplete W) :
    LiveTransition
      (shortCircuit W)
      W.initial
      ShortCircuitTransition.returnTransition := by
  intro M hReach
  have hToInitial : Reachable (shortCircuit W) M W.initial :=
    hCycle M hReach
  have hInitialToFinalOriginal : Reachable W.net W.initial W.final :=
    hOption W.initial (Reachable.refl W.initial)
  have hInitialToFinalShortCircuit :
      Reachable (shortCircuit W) W.initial W.final :=
    shortCircuit.reachable_original_to_shortCircuit W hInitialToFinalOriginal
  exact ⟨W.final,
    Reachable.trans hToInitial hInitialToFinalShortCircuit,
    shortCircuit.return_enabled_at_final W⟩

end Petri
end Pm4Lean
