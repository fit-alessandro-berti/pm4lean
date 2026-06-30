import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit

namespace Pm4Lean
namespace Petri

/-- A transition is live when every reachable marking can reach one enabling it. -/
def LiveTransition (N : Net) (M₀ : N.Marking) (t : N.Transition) : Prop :=
  ∀ M : N.Marking, Reachable N M₀ M →
    ∃ M' : N.Marking, Reachable N M M' ∧ Enabled N M' t

/-- All transitions of a marked net are live. -/
def Live (N : Net) (M₀ : N.Marking) : Prop :=
  ∀ t : N.Transition, LiveTransition N M₀ t

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
