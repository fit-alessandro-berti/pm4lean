import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Sequences

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

def ReachableNoReturn (M M' : W.Marking) : Prop :=
  ∃ ts : List (ShortCircuitTransition W),
    FiringSequence (shortCircuit W) M ts M' ∧ NoReturn W ts

theorem firingSequence_original_to_reachableNoReturn
    {M M' : W.Marking} {ts : List W.net.Transition}
    (hSeq : FiringSequence W.net M ts M') :
    ReachableNoReturn W M M' :=
  ⟨ShortCircuitTransition.ofOriginalList W ts,
    firingSequence_original_to_shortCircuit W hSeq,
    ofOriginalList_noReturn W ts⟩

theorem reachableNoReturn_projects_to_original
    {M M' : W.Marking}
    (hReach : ReachableNoReturn W M M') :
    Reachable W.net M M' := by
  obtain ⟨ts, hSeq, hNoReturn⟩ := hReach
  exact noReturn_firingSequence_reachable_projects_to_original W hNoReturn hSeq

end shortCircuit

end Petri
end Pm4Lean
