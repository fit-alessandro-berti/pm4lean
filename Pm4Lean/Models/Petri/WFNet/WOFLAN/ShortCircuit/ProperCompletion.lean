import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Reachability

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem fire_return_at_final :
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition =
      W.initial := by
  apply Marking.ext
  intro p
  calc
    fire (shortCircuit W) W.final ShortCircuitTransition.returnTransition p
        = W.final p - W.final p + W.initial p := rfl
    _ = W.initial p := by rw [Nat.sub_self, Nat.zero_add]

theorem step_preserves_original_reachable_of_proper
    (hProper : ProperCompletion W)
    {M M' : W.Marking}
    (hReachOriginal : Reachable W.net W.initial M)
    (hStep : Step (shortCircuit W) M M') :
    Reachable W.net W.initial M' := by
  exact
    @Step.rec (shortCircuit W) M
      (fun M' _ => Reachable W.net W.initial M')
      (fun {t} hEnabled =>
        match t with
        | Sum.inl t =>
            Reachable.trans hReachOriginal
              (Reachable.of_enabled (N := W.net)
                ((original_enabled_iff W M t).1 hEnabled))
        | Sum.inr u =>
            match u with
            | () =>
                have hFinalCovered : W.final ≤ M :=
                  (return_enabled_iff_final_covered W M).1 hEnabled
                have hMFinal : M = W.final :=
                  hProper M hReachOriginal hFinalCovered
                have hFireInitial :
                    fire (shortCircuit W) M
                      ShortCircuitTransition.returnTransition = W.initial := by
                  rw [hMFinal]
                  exact fire_return_at_final W
                by
                  show Reachable W.net W.initial
                    (fire (shortCircuit W) M
                      ShortCircuitTransition.returnTransition)
                  exact hFireInitial.symm ▸
                    (Reachable.refl (N := W.net) W.initial))
      M'
      hStep

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

theorem reachable_final_to_initial_in_shortCircuit :
    Reachable (shortCircuit W) W.final W.initial := by
  simpa [fire_return_at_final] using
    (Reachable.of_enabled (return_enabled_at_final W))

end shortCircuit

end Petri
end Pm4Lean
