import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBounded_mono
    {W : WFNet} {n n' : Nat}
    (hLe : n ≤ n')
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n' := by
  intro ts Mend hSeq samples hCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorsBounded_mono
      hLe (hBounded ts Mend hSeq samples hCovered)

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBounded_max_left
    {W : WFNet} {n n' : Nat}
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W (Nat.max n n') :=
  largeCoveredPrefixCutSamplesWithoutPredecessorBounded_mono
    (Nat.le_max_left n n') hBounded

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBounded_max_right
    {W : WFNet} {n n' : Nat}
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n') :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W (Nat.max n n') :=
  largeCoveredPrefixCutSamplesWithoutPredecessorBounded_mono
    (Nat.le_max_right n n') hBounded

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBounded_natListMax
    {W : WFNet} {bounds : List Nat} {n : Nat}
    (hMem : n ∈ bounds)
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W
      (NatListMax bounds) :=
  largeCoveredPrefixCutSamplesWithoutPredecessorBounded_mono
    (le_natListMax_of_mem hMem) hBounded

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_le
    {W : WFNet} {n n' : Nat}
    (hLe : n ≤ n')
    (hBounded :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W n) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  ⟨n',
    largeCoveredPrefixCutSamplesWithoutPredecessorBounded_mono
      hLe hBounded⟩

end Petri
end Pm4Lean
