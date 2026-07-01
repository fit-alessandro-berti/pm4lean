import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Bounds
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions

namespace Pm4Lean
namespace Petri

theorem exists_localBound_largeCoveredPrefixCutGreedyCoordinateBasis
    {W : WFNet} {ts : List W.net.Transition} {Mend : W.Marking}
    (hSeq : FiringSequence W.net W.initial ts Mend)
    (samples :
      List (FiringSequence.PrefixCutSample W.net W.initial ts Mend))
    (hSamplesCovered :
      FiringSequence.PrefixCutsCoveredBySamples samples) :
    ∃ k : Nat,
      ∀ coords : List Nat,
        coords ∈ natListGreedyBasis
          (FiringSequence.prefixCutSampleCoordinateLists samples) →
          ∀ x : Nat, x ∈ coords → x ≤ k := by
  have _ := hSeq
  have _ := hSamplesCovered
  exact
    FiringSequence.exists_greedyPrefixCutSampleCoordinateBasis_bound
      samples

theorem exists_localBound_largeCoveredPrefixCutNoPredecessorGreedyCoordinateBasis
    {W : WFNet} {ts : List W.net.Transition} {Mend : W.Marking}
    (hSeq : FiringSequence W.net W.initial ts Mend)
    (samples :
      List (FiringSequence.PrefixCutSample W.net W.initial ts Mend))
    (hSamplesCovered :
      FiringSequence.PrefixCutsCoveredBySamples samples) :
    ∃ k : Nat,
      ∀ coords : List Nat,
        coords ∈ natListGreedyBasis
          (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
            samples) →
          ∀ x : Nat, x ∈ coords → x ≤ k := by
  have _ := hSeq
  have _ := hSamplesCovered
  exact
    FiringSequence.exists_greedyPrefixCutNoPredecessorSampleCoordinateBasis_bound
      samples

end Petri
end Pm4Lean
