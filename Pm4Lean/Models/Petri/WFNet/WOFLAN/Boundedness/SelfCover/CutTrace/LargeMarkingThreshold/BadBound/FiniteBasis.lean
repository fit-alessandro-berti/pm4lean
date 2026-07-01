import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Monotone

namespace Pm4Lean
namespace Petri

def LargeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome
    (W : WFNet) (bounds : List Nat) : Prop :=
  ∀ ts : List W.net.Transition,
    ∀ Mend : W.Marking,
      FiringSequence W.net W.initial ts Mend →
        ∀ samples :
          List (FiringSequence.PrefixCutSample W.net W.initial ts Mend),
          FiringSequence.PrefixCutsCoveredBySamples samples →
            ∃ n : Nat,
              n ∈ bounds ∧
                FiringSequence.NoComparablePrefixCutPredecessorsBounded
                  samples n

def HasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis
    (W : WFNet) : Prop :=
  ∃ bounds : List Nat,
    LargeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome W bounds

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBounded_of_finiteBasis
    {W : WFNet} {bounds : List Nat}
    (hBasis :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome
        W bounds) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded
      W (NatListMax bounds) := by
  intro ts Mend hSeq samples hCovered
  obtain ⟨n, hMem, hBounded⟩ :=
    hBasis ts Mend hSeq samples hCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorsBounded_natListMax
      hMem hBounded

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_finiteBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W := by
  obtain ⟨bounds, hBounds⟩ := hBasis
  exact ⟨NatListMax bounds,
    largeCoveredPrefixCutSamplesWithoutPredecessorBounded_of_finiteBasis
      hBounds⟩

end Petri
end Pm4Lean
