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

end Petri
end Pm4Lean
