import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Bound
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.FiniteBasis
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions

namespace Pm4Lean
namespace Petri

theorem largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_of_coordinateCover
    {W : WFNet} {coordinates : List (List Nat)}
    (hCoordinates :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy
      W (coordinates.map (fun coords => Marking.ofValuesOn W.net.places coords)) := by
  intro ts Mend hSeq samples hSamplesCovered
  exact
    FiringSequence.noComparablePrefixCutPredecessorMarkingsDominatedBy_of_coordinateCover
      (hCoordinates ts Mend hSeq samples hSamplesCovered)

theorem hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_coordinateCover
    {W : WFNet}
    (hCoordinates :
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover W := by
  obtain ⟨coordinates, hCoveredBy⟩ := hCoordinates
  exact ⟨coordinates.map (fun coords => Marking.ofValuesOn W.net.places coords),
    largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_of_coordinateCover
      hCoveredBy⟩

theorem hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    {W : WFNet}
    (hCoordinates :
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorBound W :=
  hasLargeCoveredPrefixCutNoPredecessorBound_of_markingsDominated
    (hasLargeCoveredPrefixCutNoPredecessorMarkingDominatingCover_of_coordinateCover
      hCoordinates)

theorem largeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome_of_coordinateCover
    {W : WFNet} {coordinates : List (List Nat)}
    (hCoordinates :
      LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
        W coordinates) :
    LargeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome
      W [NatListMax
        (sampleMarkingTokenSums W.net
          (coordinates.map
            (fun coords => Marking.ofValuesOn W.net.places coords)))] :=
  largeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome_of_markingsDominated
    (largeCoveredPrefixCutSamplesWithoutPredecessorMarkingsDominatedBy_of_coordinateCover
      hCoordinates)

theorem hasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis_of_coordinateCover
    {W : WFNet}
    (hCoordinates :
      HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W) :
    HasLargeCoveredPrefixCutNoPredecessorFiniteBoundBasis W := by
  obtain ⟨coordinates, hCoveredBy⟩ := hCoordinates
  exact ⟨[NatListMax
      (sampleMarkingTokenSums W.net
        (coordinates.map
          (fun coords => Marking.ofValuesOn W.net.places coords)))],
    largeCoveredPrefixCutSamplesWithoutPredecessorBoundedBySome_of_coordinateCover
      hCoveredBy⟩

end Petri
end Pm4Lean
