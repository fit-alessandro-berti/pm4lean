import Pm4Lean.Models.Petri.Semantics.SinkLemmas
import Pm4Lean.Models.Petri.WFNet.Behavior.OptionToComplete

namespace Pm4Lean
namespace Petri

/-- If the final marking has been covered, no extra tokens remain. -/
def ProperCompletion (W : WFNet) : Prop :=
  ∀ M : W.Marking, Reachable W.net W.initial M → W.final ≤ M → M = W.final

/--
A consequence of option to complete plus a sink final place: a reachable marking
that already covers the final marking cannot contain more than one token in the
final place.  This is the provable core of the usual proper-completion argument;
excluding extra tokens in other places needs an additional invariant.
-/
theorem option_to_complete_implies_final_place_not_overmarked
    {W : WFNet} (hSink : SinkPlace W.net W.o) (hOption : OptionToComplete W)
    {M : W.Marking} (hReach : Reachable W.net W.initial M)
    (hFinalCovered : W.final ≤ M) :
    M W.o = 1 := by
  have hCanComplete : Reachable W.net M W.final := hOption M hReach
  have hMono : M W.o ≤ W.final W.o :=
    sink_place_token_monotone_reachable hSink hCanComplete
  have hLower : W.final W.o ≤ M W.o := hFinalCovered W.o
  have hUpperOne : M W.o ≤ 1 := by
    simpa [WFNet.final, Marking.singleton_self] using hMono
  have hLowerOne : 1 ≤ M W.o := by
    simpa [WFNet.final, Marking.singleton_self] using hLower
  exact Nat.le_antisymm hUpperOne hLowerOne

/--
The extra side condition needed to upgrade final-place non-overmarking to full
proper completion.  It is intentionally explicit because sink-place monotonicity
alone does not rule out extra tokens in non-final places.
-/
def NoExtraTokensAtFinalCover (W : WFNet) : Prop :=
  ∀ M : W.Marking, Reachable W.net W.initial M → W.final ≤ M →
    M W.o = 1 → M = W.final

theorem option_to_complete_implies_proper_completion
    {W : WFNet} (hSink : SinkPlace W.net W.o)
    (hNoExtra : NoExtraTokensAtFinalCover W)
    (hOption : OptionToComplete W) :
    ProperCompletion W := by
  intro M hReach hFinalCovered
  exact hNoExtra M hReach hFinalCovered
    (option_to_complete_implies_final_place_not_overmarked
      hSink hOption hReach hFinalCovered)

end Petri
end Pm4Lean
