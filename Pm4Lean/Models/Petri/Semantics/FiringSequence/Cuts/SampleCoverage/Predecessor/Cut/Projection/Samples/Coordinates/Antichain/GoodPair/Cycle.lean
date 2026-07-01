import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Prefix.Cycle
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Antichain.GoodPair.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem equalPrefixCutCycleInRun_of_noPredecessor_prefix_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor second)
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    EqualPrefixCutCycleInRun N M₀ ts Mend := by
  exact equalPrefixCutCycleInRun_of_samples_prefix_comparable_eq
    (marking_eq_of_no_comparablePrefixCutPredecessor_of_coordinateLe
      hNoPredecessor hPrefix hLe)
    (Or.inl ⟨loop, hPrefix⟩)

theorem hasComparablePrefixCutPredecessor_or_equalPrefixCutCycleInRun_of_prefix_coordinateLe
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    {loop : List N.Transition}
    (hPrefix : second.pref = first.pref ++ loop)
    (hLe :
      NatListLe (Marking.placeValues N first.marking)
        (Marking.placeValues N second.marking)) :
    HasComparablePrefixCutPredecessor second ∨
      EqualPrefixCutCycleInRun N M₀ ts Mend := by
  classical
  by_cases hPredecessor : HasComparablePrefixCutPredecessor second
  · exact Or.inl hPredecessor
  · exact Or.inr
      (equalPrefixCutCycleInRun_of_noPredecessor_prefix_coordinateLe
        hPredecessor hPrefix hLe)

theorem exists_predecessor_or_equalPrefixCutCycleInRun_of_prefixCoordinateGoodPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hPair : ContainsPrefixCoordinateGoodPair samples) :
    (∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧ HasComparablePrefixCutPredecessor sample) ∨
      EqualPrefixCutCycleInRun N M₀ ts Mend := by
  obtain ⟨first, second, loop, _hFirstMem, hSecondMem,
    hPrefix, hLe⟩ := hPair
  obtain hPredecessor | hCycle :=
    hasComparablePrefixCutPredecessor_or_equalPrefixCutCycleInRun_of_prefix_coordinateLe
      (first := first) (second := second) (loop := loop) hPrefix hLe
  · exact Or.inl ⟨second, hSecondMem, hPredecessor⟩
  · exact Or.inr hCycle

theorem equalPrefixCutCycleInRun_of_prefixCoordinateGoodPair_noPredecessors
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hPair : ContainsPrefixCoordinateGoodPair samples)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample) :
    EqualPrefixCutCycleInRun N M₀ ts Mend := by
  obtain hPredecessor | hCycle :=
    exists_predecessor_or_equalPrefixCutCycleInRun_of_prefixCoordinateGoodPair
      hPair
  · obtain ⟨sample, hMem, hHasPredecessor⟩ := hPredecessor
    exact False.elim ((hNoPredecessor sample hMem) hHasPredecessor)
  · exact hCycle

end FiringSequence
end Petri
end Pm4Lean
