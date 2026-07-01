import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.Cover.Coordinate

namespace Pm4Lean
namespace Petri

theorem woflanProofObligations_of_coordinate
    {W : WFNet}
    (hObligations : WoflanCoordinateProofObligations W) :
    WoflanProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorBound_of_coordinateCover
    hObligations.large_covered_prefix_cut_no_predecessor_coordinate_cover⟩

theorem woflanProofObligations_of_greedy
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_greedy hObligations)

theorem woflanProofObligations_of_greedy_basisCover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_greedy_basisCover hCover)

theorem woflanProofObligations_of_noPredecessorGreedy
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_noPredecessorGreedy
      hObligations)

theorem woflanProofObligations_of_noPredecessorGreedy_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_noPredecessorGreedy_basisCover
      hCover)

theorem woflanProofObligations_of_noPredecessorGreedy_lengthNormalizedBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_noPredecessorGreedy_lengthNormalizedBasisCover
      hCover)

end Petri
end Pm4Lean
