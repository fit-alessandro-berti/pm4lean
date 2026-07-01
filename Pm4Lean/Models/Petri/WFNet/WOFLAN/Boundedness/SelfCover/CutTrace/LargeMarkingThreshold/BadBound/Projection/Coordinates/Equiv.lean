import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Bridge

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_bound
    {W : WFNet} {k : Nat}
    (hBound :
      LargeCoveredPrefixCutSamplesWithoutPredecessorBounded W k) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W (NatListsUpTo W.net.places.length k) := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorCoordinateListsDominatedBy_boundedBox
      (hBound ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_bound
    {W : WFNet}
    (hBound : HasLargeCoveredPrefixCutNoPredecessorBound W) :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W := by
  obtain ⟨k, hBoundAtK⟩ := hBound
  exact ⟨NatListsUpTo W.net.places.length k,
    largeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy_of_bound
      hBoundAtK⟩

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_coordinateDominatingCover
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_bound,
    hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover⟩

end Petri
end Pm4Lean
