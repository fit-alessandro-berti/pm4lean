import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Basic

namespace Pm4Lean
namespace Petri

/-- The original WF-net has a global token bound on markings reachable from
its initial marking. -/
def TokenBoundedReachableOriginal (W : WFNet) : Prop :=
  ∃ k : Nat, ∀ M : W.Marking, Reachable W.net W.initial M →
    ∀ p : W.net.Place, M p ≤ k

/-- The original WF-net has a global bound on the total tokens over its place
enumeration. -/
def TokenSumBoundedReachableOriginal (W : WFNet) : Prop :=
  TokenSumBoundedReachable W.net W.initial

theorem original_bounded_of_tokenSumBoundedReachableOriginal
    {W : WFNet}
    (hTokenSumBounded : TokenSumBoundedReachableOriginal W) :
    TokenBoundedReachableOriginal W := by
  obtain ⟨k, hBoundSum⟩ := hTokenSumBounded
  exact ⟨k, fun M hReach p =>
    Nat.le_trans
      (Marking.le_tokenSumOn_of_complete
        W.net.places W.net.places_complete M p)
      (hBoundSum M hReach)⟩

theorem tokenSumBoundedReachableOriginal_of_original_bounded
    {W : WFNet}
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    TokenSumBoundedReachableOriginal W := by
  obtain ⟨k, hBoundOriginalBy⟩ := hBoundOriginal
  exact ⟨W.net.places.length * k, fun M hReach =>
    Marking.tokenSumOn_le_length_mul_of_forall_le
      W.net.places M k (fun p => hBoundOriginalBy M hReach p)⟩

theorem original_bounded_iff_tokenSumBoundedReachableOriginal
    {W : WFNet} :
    TokenBoundedReachableOriginal W ↔
      TokenSumBoundedReachableOriginal W :=
  ⟨tokenSumBoundedReachableOriginal_of_original_bounded,
    original_bounded_of_tokenSumBoundedReachableOriginal⟩

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
