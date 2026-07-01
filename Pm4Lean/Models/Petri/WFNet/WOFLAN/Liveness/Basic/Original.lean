import Pm4Lean.Models.Petri.Behavior.Liveness
import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit

namespace Pm4Lean
namespace Petri

theorem return_live_from_original_reachable
    {W : WFNet} (hOption : OptionToComplete W) :
    ∀ M : W.Marking, Reachable W.net W.initial M →
      ∃ M' : W.Marking,
        Reachable (shortCircuit W) M M' ∧
          Enabled (shortCircuit W) M'
            ShortCircuitTransition.returnTransition := by
  intro M hReach
  exact ⟨W.final,
    shortCircuit.reachable_original_to_shortCircuit W (hOption M hReach),
    shortCircuit.return_enabled_at_final W⟩

theorem original_transition_eventually_enabled_from_initial
    {W : WFNet} (hNoDead : NoDeadTransitions W)
    (t : W.net.Transition) :
    ∃ M : W.Marking,
      Reachable (shortCircuit W) W.initial M ∧
        Enabled (shortCircuit W) M
          (ShortCircuitTransition.original t) := by
  obtain ⟨M, hReach, hEnabled⟩ := hNoDead t
  exact ⟨M,
    shortCircuit.reachable_original_to_shortCircuit W hReach,
    (shortCircuit.original_enabled_iff W M t).2 hEnabled⟩

end Petri
end Pm4Lean
