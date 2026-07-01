import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions.Bound

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome
    (W : WFNet) (bounds : List Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            ∃ k : Nat,
              k ∈ bounds ∧
                ∀ coords : List Nat,
                  coords ∈ natListGreedyBasis
                    (FiringSequence.prefixCutSampleCoordinateLists samples) →
                      ∀ x : Nat, x ∈ coords → x ≤ k

def LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome
    (W : WFNet) (bounds : List Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            ∃ k : Nat,
              k ∈ bounds ∧
                ∀ coords : List Nat,
                  coords ∈ natListGreedyBasis
                    (FiringSequence.prefixCutNoPredecessorSampleCoordinateLists
                      samples) →
                      ∀ x : Nat, x ∈ coords → x ≤ k

def HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis
    (W : WFNet) : Prop :=
  ∃ bounds : List Nat,
    LargeCoveredPrefixCutGreedyCoordinateBasesBoundedBySome W bounds

def HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
    (W : WFNet) : Prop :=
  ∃ bounds : List Nat,
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesBoundedBySome
      W bounds

end Petri
end Pm4Lean
