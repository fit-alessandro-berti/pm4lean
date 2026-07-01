import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.PrefixOrder
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Negative

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem marking_eq_of_no_comparablePrefixCutPredecessor
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe : first.marking ≤ second.marking) :
    first.marking = second.marking := by
  exact Classical.byContradiction (fun hNe =>
    hNoPredecessor
      ⟨first.pref, loop, first.marking,
        hPrefix, first.isCut, hLe, hNe⟩)

theorem not_comparablePrefixCutSamplePair_of_no_cut_predecessor
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second) :
    ¬ ComparablePrefixCutSamplePair first second := by
  intro hPair
  obtain ⟨loop, hPrefix, hLe, hNe⟩ := hPair
  exact hNoPredecessor
    ⟨first.pref, loop, first.marking,
      hPrefix, first.isCut, hLe, hNe⟩

theorem eq_or_exists_gt_of_le_no_comparablePrefixCutPredecessors
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hNoFirst : ¬ HasComparablePrefixCutPredecessor first)
    (hNoSecond : ¬ HasComparablePrefixCutPredecessor second)
    (hLe : first.marking ≤ second.marking) :
    first.marking = second.marking ∨
      ∃ p : N.Place, first.marking p < second.marking p := by
  obtain hSecondExtends | hFirstExtends :=
    prefixCutSamples_prefix_comparable first second
  · left
    obtain ⟨loop, hSecondExtends⟩ := hSecondExtends
    exact marking_eq_of_no_comparablePrefixCutPredecessor
      (loop := loop) hNoSecond hSecondExtends hLe
  · obtain hEq | hGt :=
      let ⟨loop, hFirstExtends⟩ := hFirstExtends
      eq_or_exists_gt_of_no_comparablePrefixCutPredecessor
        (second := first)
        (loop := loop) hNoFirst hFirstExtends second.isCut
    · exact Or.inl hEq.symm
    · exact Or.inr hGt

end FiringSequence
end Petri
end Pm4Lean
