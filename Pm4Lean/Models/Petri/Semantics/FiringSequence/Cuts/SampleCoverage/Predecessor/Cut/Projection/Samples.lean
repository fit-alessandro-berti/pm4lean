import Pm4Lean.Models.Petri.Behavior.Boundedness.Samples.ExplicitBound
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def prefixCutSampleMarkings
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : List N.Marking :=
  samples.map (fun sample => sample.marking)

theorem noComparablePrefixCutPredecessorMarkingsCovered_by_sampleMarkings
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorMarkingsCovered samples
      (prefixCutSampleMarkings samples) := by
  intro sample hSampleMem _hNoPredecessor
  exact ⟨sample.marking, by
    simp [prefixCutSampleMarkings]
    exact ⟨sample, hSampleMem, rfl⟩,
    rfl⟩

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_sampleMarkings
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples
      (prefixCutSampleMarkings samples) :=
  noComparablePrefixCutPredecessorMarkingsDominatedBy_of_covered
    (noComparablePrefixCutPredecessorMarkingsCovered_by_sampleMarkings
      samples)

theorem exists_noComparablePrefixCutPredecessorMarkingsDominatedBy
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∃ markings : List N.Marking,
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings :=
  ⟨prefixCutSampleMarkings samples,
    noComparablePrefixCutPredecessorMarkingsDominatedBy_sampleMarkings
      samples⟩

theorem exists_noComparablePrefixCutPredecessorsBounded
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∃ k : Nat, NoComparablePrefixCutPredecessorsBounded samples k :=
  ⟨NatListMax (sampleMarkingTokenSums N (prefixCutSampleMarkings samples)),
    noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    (noComparablePrefixCutPredecessorMarkingsDominatedBy_sampleMarkings
      samples)
    (fun _ hMem =>
      sampleMarking_le_natListMax_tokenSums
        (N := N) (samples := prefixCutSampleMarkings samples) hMem)⟩

theorem noComparablePrefixCutPredecessorsBounded_by_sampleMarkingTokenSums
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorsBounded samples
      (NatListMax
        (sampleMarkingTokenSums N (prefixCutSampleMarkings samples))) :=
  noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    (noComparablePrefixCutPredecessorMarkingsDominatedBy_sampleMarkings
      samples)
    (fun _ hMem =>
      sampleMarking_le_natListMax_tokenSums
        (N := N) (samples := prefixCutSampleMarkings samples) hMem)

end FiringSequence
end Petri
end Pm4Lean
