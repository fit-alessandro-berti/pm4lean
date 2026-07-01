import Pm4Lean.Models.Petri.WFNet.WOFLAN.Liveness.Basic

namespace Pm4Lean
namespace Petri

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

end Petri
end Pm4Lean
