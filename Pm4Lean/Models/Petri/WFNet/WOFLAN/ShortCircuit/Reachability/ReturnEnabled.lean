import Pm4Lean.Models.Petri.WFNet.WOFLAN.ShortCircuit.Reachability.Original

namespace Pm4Lean
namespace Petri
namespace shortCircuit

variable (W : WFNet)

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
