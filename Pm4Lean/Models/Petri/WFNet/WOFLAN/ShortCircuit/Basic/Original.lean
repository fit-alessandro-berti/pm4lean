import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Basic.Definition

namespace Pm4Lean
namespace Petri

namespace shortCircuit

variable (W : WFNet)

theorem original_enabled_iff (M : W.Marking) (t : W.net.Transition) :
    Enabled (shortCircuit W) M (ShortCircuitTransition.original t) ↔
      Enabled W.net M t :=
  Iff.rfl

theorem fire_original (M : W.Marking) (t : W.net.Transition) :
    fire (shortCircuit W) M (ShortCircuitTransition.original t) =
      fire W.net M t :=
  rfl

theorem step_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Step (shortCircuit W) M (fire W.net M t) :=
  Step.fire ((original_enabled_iff W M t).2 hEnabled)

theorem step_original_to_shortCircuit {M M' : W.Marking}
    (hStep : Step W.net M M') :
    Step (shortCircuit W) M M' := by
  cases hStep with
  | fire hEnabled =>
      simpa [fire_original] using step_original_of_enabled W hEnabled

theorem reachable_original_of_enabled {M : W.Marking} {t : W.net.Transition}
    (hEnabled : Enabled W.net M t) :
    Reachable (shortCircuit W) M (fire W.net M t) :=
  Reachable.of_step (step_original_of_enabled W hEnabled)

end shortCircuit

end Petri
end Pm4Lean
