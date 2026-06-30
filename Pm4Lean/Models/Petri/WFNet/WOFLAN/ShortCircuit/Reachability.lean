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

theorem reachableNoReturn_to_return_enabled_gives_original_reach_to_cover
    {M M' : W.Marking}
    (hReach : ReachableNoReturn W M M')
    (hReturnEnabled :
      Enabled (shortCircuit W) M'
        ShortCircuitTransition.returnTransition) :
    ∃ Mcover : W.Marking,
      Reachable W.net M Mcover ∧ W.final ≤ Mcover :=
  ⟨M',
    reachableNoReturn_projects_to_original W hReach,
    (return_enabled_iff_final_covered W M').1 hReturnEnabled⟩

theorem reachable_to_return_enabled_gives_original_reach_to_cover
    {M M' : W.Marking}
    (hReachSC : Reachable (shortCircuit W) M M')
    (hReturnEnabled :
      Enabled (shortCircuit W) M'
        ShortCircuitTransition.returnTransition) :
    ∃ Mcover : W.Marking,
      Reachable W.net M Mcover ∧ W.final ≤ Mcover := by
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReachSC
  obtain ⟨Mcover, pref, hPrefixSeq, hNoReturn, hPrefixReturnEnabled⟩ :=
    firingSequence_to_return_enabled_has_noReturn_prefix W hSeq hReturnEnabled
  exact ⟨Mcover,
    noReturn_firingSequence_reachable_projects_to_original
      W hNoReturn hPrefixSeq,
    (return_enabled_iff_final_covered W Mcover).1 hPrefixReturnEnabled⟩

end shortCircuit

end Petri
end Pm4Lean
