import Pm4Lean.Models.Petri.Behavior.Boundedness
import Pm4Lean.Models.Petri.WFNet.Soundness.Soundness

namespace Pm4Lean
namespace Petri

/-- The original WF-net has a global token bound on markings reachable from
its initial marking. -/
abbrev TokenBoundedReachableOriginal (W : WFNet) : Prop :=
  Bounded W.net W.initial

/-- The original WF-net has a global bound on the total tokens over its place
enumeration. -/
abbrev TokenSumBoundedReachableOriginal (W : WFNet) : Prop :=
  TokenSumBoundedReachable W.net W.initial

theorem original_bounded_of_tokenSumBoundedReachableOriginal
    {W : WFNet}
    (hTokenSumBounded : TokenSumBoundedReachableOriginal W) :
    TokenBoundedReachableOriginal W :=
  bounded_of_tokenSumBoundedReachable hTokenSumBounded

theorem tokenSumBoundedReachableOriginal_of_original_bounded
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    TokenSumBoundedReachableOriginal W :=
  tokenSumBoundedReachable_of_bounded hBoundOriginal

theorem original_bounded_iff_tokenSumBoundedReachableOriginal
    {W : WFNet} :
    TokenBoundedReachableOriginal W ↔
      TokenSumBoundedReachableOriginal W :=
  bounded_iff_tokenSumBoundedReachable

end Petri
end Pm4Lean
