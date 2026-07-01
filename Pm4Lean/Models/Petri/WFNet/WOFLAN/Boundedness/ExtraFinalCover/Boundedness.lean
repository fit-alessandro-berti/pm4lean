import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.ExtraFinalCover.Return

namespace Pm4Lean
namespace Petri

theorem hasExtraTokensAtFinalCover_not_boundedBy_initial_token
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      ¬ BoundedBy (shortCircuit W) W.initial (W.initial p) := by
  obtain ⟨M', hReach, p, hGt⟩ :=
    hasExtraTokensAtFinalCover_reachable_after_return_exceeds_initial
      hExtra
  exact ⟨p, not_boundedBy_of_reachable_gt hReach hGt⟩

end Petri
end Pm4Lean
