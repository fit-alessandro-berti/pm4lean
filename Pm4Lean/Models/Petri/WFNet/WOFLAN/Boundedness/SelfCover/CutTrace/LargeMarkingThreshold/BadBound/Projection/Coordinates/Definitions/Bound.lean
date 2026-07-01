import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions.Cover

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy
    (W : WFNet) (k : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            ∀ coords : List Nat,
              coords ∈ natListGreedyBasis
                (FiringSequence.prefixCutSampleCoordinateLists samples) →
                  ∀ x : Nat, x ∈ coords → x ≤ k

def LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy
    (W : WFNet) (k : Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            ∀ coords : List Nat,
              coords ∈ natListGreedyBasis
                (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                  samples) →
                  ∀ x : Nat, x ∈ coords → x ≤ k

def HasLargeCoveredPrefixCutGreedyCoordinateBasisBound
    (W : WFNet) : Prop :=
  ∃ k : Nat, LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBy W k

def HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound
    (W : WFNet) : Prop :=
  ∃ k : Nat,
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBy W k

end Petri
end Pm4Lean
