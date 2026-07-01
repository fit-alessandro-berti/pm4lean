import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.ProperCompletion.Step

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem firingSequence_preserves_original_reachable_of_proper
    (hProper : ProperCompletion W)
    {M M' : W.Marking} {ts : List (ShortCircuitTransition W)}
    (hReachOriginal : Reachable W.net W.initial M)
    (hSeq : FiringSequence (shortCircuit W) M ts M') :
    Reachable W.net W.initial M' := by
  exact
    FiringSequence.rec (N := shortCircuit W)
      (motive := fun M _ts M' _ =>
        Reachable W.net W.initial M → Reachable W.net W.initial M')
      (fun M hReachOriginal => hReachOriginal)
      (fun hEnabled _hTail ih hReachOriginal =>
        ih
          (step_preserves_original_reachable_of_proper
            W hProper hReachOriginal (Step.fire hEnabled)))
      hSeq
      hReachOriginal

theorem reachable_shortCircuit_to_original_of_proper
    (hProper : ProperCompletion W)
    {M : W.Marking}
    (hReachSC : Reachable (shortCircuit W) W.initial M) :
    Reachable W.net W.initial M := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReachSC
  exact firingSequence_preserves_original_reachable_of_proper
    W hProper (Reachable.refl W.initial) hSeq

end shortCircuit

end Petri
end Pm4Lean
