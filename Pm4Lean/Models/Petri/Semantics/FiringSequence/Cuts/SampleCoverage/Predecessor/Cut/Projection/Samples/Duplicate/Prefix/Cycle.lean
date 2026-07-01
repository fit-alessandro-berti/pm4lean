import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Prefix.Cycle
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Duplicate.Prefix

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem equalPrefixCutCycleInRun_of_repeatedComparableMembers
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hMembers :
      ContainsRepeatedPrefixCutSampleMarkingComparableMembers samples) :
    EqualPrefixCutCycleInRun N M₀ ts Mend := by
  obtain ⟨first, second, _hFirstMem, _hSecondMem, hEq, hComparable⟩ :=
    hMembers
  exact equalPrefixCutCycleInRun_of_samples_prefix_comparable_eq
    hEq hComparable

theorem equalPrefixCutCycleInRun_of_noPredecessor_length_gt
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    EqualPrefixCutCycleInRun N M₀ ts Mend :=
  equalPrefixCutCycleInRun_of_repeatedComparableMembers
    (containsRepeatedPrefixCutSampleMarkingComparableMembers_of_noPredecessor_length_gt
      hLength hNoPredecessor hBounded)

end FiringSequence
end Petri
end Pm4Lean
