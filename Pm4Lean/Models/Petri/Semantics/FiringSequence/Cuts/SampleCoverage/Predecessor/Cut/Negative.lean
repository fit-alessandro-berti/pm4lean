import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem eq_or_exists_gt_of_no_comparablePrefixCutPredecessor
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {second : PrefixCutSample N M₀ ts Mend}
    {pref loop : List N.Transition} {M : N.Marking}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second)
    (hSecondPref : second.pref = pref ++ loop)
    (hCut : PrefixCutInRun N M₀ ts Mend pref M) :
    M = second.marking ∨ ∃ p : N.Place, second.marking p < M p := by
  classical
  by_cases hEq : M = second.marking
  · exact Or.inl hEq
  · right
    by_cases hLe : M ≤ second.marking
    · exact False.elim
        (hNoPredecessor ⟨pref, loop, M, hSecondPref, hCut, hLe, hEq⟩)
    · by_cases hExists : ∃ p : N.Place, second.marking p < M p
      · exact hExists
      · exact False.elim (hLe (by
          intro p
          exact Nat.le_of_not_gt (by
            intro hLt
            exact hExists ⟨p, hLt⟩)))

end FiringSequence
end Petri
end Pm4Lean
