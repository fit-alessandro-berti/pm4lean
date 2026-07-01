import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.PrefixOrder
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Duplicate

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def ContainsRepeatedPrefixCutSampleMarkingPrefixComparablePair
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∃ first second : PrefixCutSample N M₀ ts Mend,
    ∃ before between after :
      List (PrefixCutSample N M₀ ts Mend),
      samples = before ++ first :: between ++ second :: after ∧
        first.marking = second.marking ∧
          ((∃ loop, second.pref = first.pref ++ loop) ∨
            ∃ loop, first.pref = second.pref ++ loop)

def ContainsRepeatedPrefixCutSampleMarkingComparableMembers
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∃ first second : PrefixCutSample N M₀ ts Mend,
    first ∈ samples ∧
      second ∈ samples ∧
        first.marking = second.marking ∧
          ((∃ loop, second.pref = first.pref ++ loop) ∨
            ∃ loop, first.pref = second.pref ++ loop)

theorem containsRepeatedPrefixCutSampleMarkingPrefixComparablePair_of_repeatedPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hRepeated : ContainsRepeatedPrefixCutSampleMarkingPair samples) :
    ContainsRepeatedPrefixCutSampleMarkingPrefixComparablePair samples := by
  obtain ⟨first, second, before, between, after, hSplit, hEq⟩ :=
    hRepeated
  exact ⟨first, second, before, between, after,
    hSplit, hEq, prefixCutSamples_prefix_comparable first second⟩

theorem containsRepeatedPrefixCutSampleMarkingComparableMembers_of_prefixPair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hPair :
      ContainsRepeatedPrefixCutSampleMarkingPrefixComparablePair samples) :
    ContainsRepeatedPrefixCutSampleMarkingComparableMembers samples := by
  obtain ⟨first, second, before, between, after,
    hSplit, hEq, hComparable⟩ := hPair
  have hFirstMem : first ∈ samples := by
    rw [hSplit]
    simp
  have hSecondMem : second ∈ samples := by
    rw [hSplit]
    simp
  exact ⟨first, second, hFirstMem, hSecondMem, hEq, hComparable⟩

theorem containsRepeatedPrefixCutSampleMarkingPrefixComparablePair_of_noPredecessor_length_gt
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    ContainsRepeatedPrefixCutSampleMarkingPrefixComparablePair samples :=
  containsRepeatedPrefixCutSampleMarkingPrefixComparablePair_of_repeatedPair
    (containsRepeatedPrefixCutSampleMarkingPair_of_noPredecessor_length_gt
      hLength hNoPredecessor hBounded)

theorem containsRepeatedPrefixCutSampleMarkingComparableMembers_of_noPredecessor_length_gt
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLength : (NatListsUpTo N.places.length k).length < samples.length)
    (hNoPredecessor :
      ∀ sample : PrefixCutSample N M₀ ts Mend,
        sample ∈ samples → ¬ HasComparablePrefixCutPredecessor sample)
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    ContainsRepeatedPrefixCutSampleMarkingComparableMembers samples :=
  containsRepeatedPrefixCutSampleMarkingComparableMembers_of_prefixPair
    (containsRepeatedPrefixCutSampleMarkingPrefixComparablePair_of_noPredecessor_length_gt
      hLength hNoPredecessor hBounded)

end FiringSequence
end Petri
end Pm4Lean
