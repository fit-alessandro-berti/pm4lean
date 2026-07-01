import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Definitions

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
    (W : WFNet) (coordinates : List (List Nat)) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
              samples coordinates

def LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy
    (W : WFNet) (coordinates : List (List Nat)) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            NatListBasisDominatesAll
              (natListGreedyBasis
                (FiringSequence.prefixCutSampleCoordinateLists samples))
              coordinates

def LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
    (W : WFNet) (coordinates : List (List Nat)) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            NatListBasisDominatesAll
              (natListGreedyBasis
                (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                  samples))
              coordinates

end Petri
end Pm4Lean
