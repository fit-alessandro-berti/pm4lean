import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Reachability.NoReturn

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

theorem reachable_original_to_shortCircuit {M M' : W.Marking}
    (hReach : Reachable W.net M M') :
    Reachable (shortCircuit W) M M' := by
  induction hReach with
  | refl M =>
      exact Reachable.refl (N := shortCircuit W) M
  | step hStep hReach ih =>
      exact Reachable.step (step_original_to_shortCircuit W hStep) ih

theorem reachable_original_to_reachableNoReturn {M M' : W.Marking}
    (hReach : Reachable W.net M M') :
    ReachableNoReturn W M M' := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
  exact firingSequence_original_to_reachableNoReturn W hSeq

theorem reachableNoReturn_iff_original {M M' : W.Marking} :
    ReachableNoReturn W M M' ↔ Reachable W.net M M' :=
  ⟨reachableNoReturn_projects_to_original W,
    reachable_original_to_reachableNoReturn W⟩

end shortCircuit

end Petri
end Pm4Lean
