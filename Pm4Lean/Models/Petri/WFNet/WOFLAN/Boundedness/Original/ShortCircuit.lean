import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Original.Tokens
import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.ProperCompletion

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    TokenBoundedReachableOriginal W := by
  obtain ⟨k, hBoundedBy⟩ := hBounded
  exact ⟨k, fun M hReach p =>
    hBoundedBy M
      (shortCircuit.reachable_original_to_shortCircuit W hReach)
      p⟩

theorem original_tokenSum_bounded_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    TokenSumBoundedReachableOriginal W :=
  tokenSumBoundedReachableOriginal_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem shortCircuit_bounded_of_original_bounded_and_proper
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hProper : ProperCompletion W) :
    Bounded (shortCircuit W) W.initial := by
  obtain ⟨k, hBoundOriginalBy⟩ := hBoundOriginal
  exact ⟨k, fun M hReachSC p =>
    hBoundOriginalBy M
      (shortCircuit.reachable_shortCircuit_to_original_of_proper
        W hProper hReachSC)
      p⟩

theorem shortCircuit_bounded_of_original_tokenSum_bounded_and_proper
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hProper : ProperCompletion W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_bounded_and_proper
    (original_bounded_of_tokenSumBoundedReachableOriginal
      hBoundOriginal)
    hProper

theorem shortCircuit_bounded_of_original_bounded_and_sound
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W)
    (hSound : Sound W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_bounded_and_proper
    hBoundOriginal hSound.2.1

theorem shortCircuit_bounded_of_original_tokenSum_bounded_and_sound
    {W : WFNet}
    (hBoundOriginal : TokenSumBoundedReachableOriginal W)
    (hSound : Sound W) :
    Bounded (shortCircuit W) W.initial :=
  shortCircuit_bounded_of_original_tokenSum_bounded_and_proper
    hBoundOriginal hSound.2.1

end Petri
end Pm4Lean
