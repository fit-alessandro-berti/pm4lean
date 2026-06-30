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

theorem live_return_implies_option_to_cover
    {W : WFNet}
    (hLiveReturn :
      LiveTransition
        (shortCircuit W)
        W.initial
        ShortCircuitTransition.returnTransition) :
    ∀ M : W.Marking, Reachable W.net W.initial M →
      ∃ Mcover : W.Marking,
        Reachable W.net M Mcover ∧ W.final ≤ Mcover := by
  intro M hReachOriginal
  have hReachShortCircuit :
      Reachable (shortCircuit W) W.initial M :=
    shortCircuit.reachable_original_to_shortCircuit W hReachOriginal
  obtain ⟨M', hReachToReturn, hReturnEnabled⟩ :=
    hLiveReturn M hReachShortCircuit
  exact shortCircuit.reachable_to_return_enabled_gives_original_reach_to_cover
    W hReachToReturn hReturnEnabled

theorem option_to_cover_and_proper_completion_implies_option_to_complete
    {W : WFNet}
    (hCover :
      ∀ M : W.Marking, Reachable W.net W.initial M →
        ∃ Mcover : W.Marking,
          Reachable W.net M Mcover ∧ W.final ≤ Mcover)
    (hProper : ProperCompletion W) :
    OptionToComplete W := by
  intro M hReach
  obtain ⟨Mcover, hReachCover, hFinalCovered⟩ := hCover M hReach
  have hInitialToCover : Reachable W.net W.initial Mcover :=
    Reachable.trans hReach hReachCover
  have hCoverEqFinal : Mcover = W.final :=
    hProper Mcover hInitialToCover hFinalCovered
  simpa [hCoverEqFinal] using hReachCover

theorem live_return_and_proper_completion_implies_option_to_complete
    {W : WFNet}
    (hLiveReturn :
      LiveTransition
        (shortCircuit W)
        W.initial
        ShortCircuitTransition.returnTransition)
    (hProper : ProperCompletion W) :
    OptionToComplete W :=
  option_to_cover_and_proper_completion_implies_option_to_complete
    (live_return_implies_option_to_cover hLiveReturn)
    hProper

theorem live_shortCircuit_and_proper_completion_implies_option_to_complete
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hProper : ProperCompletion W) :
    OptionToComplete W :=
  live_return_and_proper_completion_implies_option_to_complete
    (hLive ShortCircuitTransition.returnTransition)
    hProper

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
