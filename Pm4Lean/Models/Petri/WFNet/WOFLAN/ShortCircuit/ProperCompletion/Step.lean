import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.ProperCompletion.Return

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

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

end shortCircuit

end Petri
end Pm4Lean
