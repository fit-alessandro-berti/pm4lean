import Pm4Lean.Models.Petri.Behavior.Liveness
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Pumping

namespace Pm4Lean
namespace Petri

/--
In a bounded short-circuited WF-net, no reachable original marking can cover
the final marking while carrying extra tokens.
-/
def ShortCircuitBoundedExcludesExtraFinalCover (W : WFNet) : Prop :=
  Live (shortCircuit W) W.initial →
    Bounded (shortCircuit W) W.initial →
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M

theorem shortCircuit_bounded_excludes_extra_final_cover
    {W : WFNet} :
    ShortCircuitBoundedExcludesExtraFinalCover W := by
  intro _hLive hBounded M hExtra
  exact extra_final_cover_closedFormStep_implies_shortCircuit_unbounded
    hExtra extra_final_cover_implies_closedFormStep hBounded

end Petri
end Pm4Lean
