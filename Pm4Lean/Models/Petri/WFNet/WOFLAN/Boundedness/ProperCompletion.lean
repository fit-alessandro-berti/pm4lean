import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.Exclusion

namespace Pm4Lean
namespace Petri

theorem proper_completion_iff_no_extra_tokens_at_final_cover
    (W : WFNet) :
    ProperCompletion W ↔
      ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M := by
  constructor
  · intro hProper M hExtra
    exact hExtra.2.2 (hProper M hExtra.1 hExtra.2.1)
  · intro hNoExtra M hReach hFinalCovered
    classical
    by_cases hEq : M = W.final
    · exact hEq
    · exact False.elim (hNoExtra M ⟨hReach, hFinalCovered, hEq⟩)

theorem not_proper_completion_iff_exists_extra_tokens_at_final_cover
    (W : WFNet) :
    ¬ ProperCompletion W ↔
      ∃ M : W.Marking, HasExtraTokensAtFinalCover W M := by
  classical
  rw [proper_completion_iff_no_extra_tokens_at_final_cover W]
  constructor
  · intro hNotAllNoExtra
    by_cases hExists : ∃ M : W.Marking, HasExtraTokensAtFinalCover W M
    · exact hExists
    · exact False.elim (hNotAllNoExtra (by
        intro M hExtra
        exact hExists ⟨M, hExtra⟩))
  · intro hExists hAllNoExtra
    obtain ⟨M, hExtra⟩ := hExists
    exact hAllNoExtra M hExtra

theorem no_extra_tokens_at_final_cover_implies_proper_completion
    {W : WFNet}
    (hNoExtra : ∀ M : W.Marking, ¬ HasExtraTokensAtFinalCover W M) :
    ProperCompletion W :=
  (proper_completion_iff_no_extra_tokens_at_final_cover W).2 hNoExtra

theorem bounded_shortCircuit_implies_proper_completion
    {W : WFNet}
    (hLive : Live (shortCircuit W) W.initial)
    (hBounded : Bounded (shortCircuit W) W.initial) :
    ProperCompletion W :=
  no_extra_tokens_at_final_cover_implies_proper_completion
    (shortCircuit_bounded_excludes_extra_final_cover hLive hBounded)

end Petri
end Pm4Lean
