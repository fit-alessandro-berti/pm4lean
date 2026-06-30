import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Original

namespace Pm4Lean
namespace Petri

/-- A reachable final-cover marking that is not exactly the final marking. -/
def HasExtraTokensAtFinalCover (W : WFNet) (M : W.Marking) : Prop :=
  Reachable W.net W.initial M ∧ W.final ≤ M ∧ M ≠ W.final

theorem hasExtraTokensAtFinalCover_exists_strict_extra
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place, W.final p < M p :=
  Marking.exists_lt_of_le_ne hExtra.2.1 hExtra.2.2.symm

theorem hasExtraTokensAtFinalCover_exists_positive_remainder
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place, 0 < M p - W.final p := by
  obtain ⟨p, hStrict⟩ :=
    hasExtraTokensAtFinalCover_exists_strict_extra hExtra
  exact ⟨p, Nat.sub_pos_of_lt hStrict⟩

theorem hasExtraTokensAtFinalCover_reachable_after_return
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    Reachable (shortCircuit W) W.initial
      (M - W.final + W.initial) := by
  exact Reachable.trans
    (shortCircuit.reachable_original_to_shortCircuit W hExtra.1)
    (shortCircuit.reachable_fire_return_of_final_covered W hExtra.2.1)

theorem hasExtraTokensAtFinalCover_return_has_positive_token
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      0 <
        fire (shortCircuit W) M
          ShortCircuitTransition.returnTransition p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    shortCircuit.fire_return_positive_of_positive_remainder
      W hPositive⟩

theorem hasExtraTokensAtFinalCover_return_exceeds_initial
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      W.initial p <
        fire (shortCircuit W) M
          ShortCircuitTransition.returnTransition p := by
  obtain ⟨p, hPositive⟩ :=
    hasExtraTokensAtFinalCover_exists_positive_remainder hExtra
  exact ⟨p,
    shortCircuit.initial_lt_fire_return_of_positive_remainder
      W hPositive⟩

theorem hasExtraTokensAtFinalCover_reachable_after_return_exceeds_initial
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ M' : W.Marking,
      Reachable (shortCircuit W) W.initial M' ∧
        ∃ p : W.net.Place, W.initial p < M' p := by
  exact ⟨M - W.final + W.initial,
    hasExtraTokensAtFinalCover_reachable_after_return hExtra,
    by
      simpa [shortCircuit.fire_return] using
        hasExtraTokensAtFinalCover_return_exceeds_initial hExtra⟩

theorem hasExtraTokensAtFinalCover_not_boundedBy_initial_token
    {W : WFNet} {M : W.Marking}
    (hExtra : HasExtraTokensAtFinalCover W M) :
    ∃ p : W.net.Place,
      ¬ BoundedBy (shortCircuit W) W.initial (W.initial p) := by
  obtain ⟨M', hReach, p, hGt⟩ :=
    hasExtraTokensAtFinalCover_reachable_after_return_exceeds_initial
      hExtra
  exact ⟨p, not_boundedBy_of_reachable_gt hReach hGt⟩

end Petri
end Pm4Lean
