import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Monotone
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsCoveredBy
    (W : WFNet) (markings : List W.Marking) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.NoComparablePrefixCutPredecessorMarkingsCovered
              samples markings

def LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
    (W : WFNet) (markings : List W.Marking) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            FiringSequence.NoComparablePrefixCutPredecessorMarkingsDominatedBy
              samples markings

def HasLargeCoveredPrefixCutNoPredecessorMarkingCover
    (W : WFNet) : Prop :=
  ∃ markings : List W.Marking,
    LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsCoveredBy
      W markings

def HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover
    (W : WFNet) : Prop :=
  ∃ markings : List W.Marking,
    LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
      W markings

end Petri
end Pm4Lean
