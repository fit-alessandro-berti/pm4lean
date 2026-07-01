import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Enumeration
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem prefixCutSamples_with_markingCover_exists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    ∃ samples : List (PrefixCutSample N M₀ ts Mend),
      ∃ markings : List N.Marking,
        PrefixCutsCoveredBySamples samples ∧
          NoComparablePrefixCutPredecessorMarkingsDominatedBy
            samples markings := by
  obtain ⟨samples, hCovered⟩ := prefixCutSamples_cover_exists hRun
  exact ⟨samples, prefixCutSampleMarkings samples, hCovered,
    noComparablePrefixCutPredecessorMarkingsDominatedBy_sampleMarkings
      samples⟩

theorem prefixCutSamples_with_noPredecessorBound_exists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    ∃ samples : List (PrefixCutSample N M₀ ts Mend),
      ∃ k : Nat,
        PrefixCutsCoveredBySamples samples ∧
          NoComparablePrefixCutPredecessorsBounded samples k := by
  obtain ⟨samples, hCovered⟩ := prefixCutSamples_cover_exists hRun
  exact ⟨samples,
    NatListMax
      (sampleMarkingTokenSums N (prefixCutSampleMarkings samples)),
    hCovered,
    noComparablePrefixCutPredecessorsBounded_by_sampleMarkingTokenSums
      samples⟩

end FiringSequence
end Petri
end Pm4Lean
