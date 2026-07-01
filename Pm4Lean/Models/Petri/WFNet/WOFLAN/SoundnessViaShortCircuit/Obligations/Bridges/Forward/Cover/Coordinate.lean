import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.Cover.Records

namespace Pm4Lean
namespace Petri

theorem woflanCoordinateProofObligations_of_greedy
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateProofObligations W) :
    WoflanCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyBasisCover
    hObligations.large_covered_prefix_cut_greedy_coordinate_basis_cover⟩

theorem woflanCoordinateProofObligations_of_greedy_basisCover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    WoflanCoordinateProofObligations W :=
  woflanCoordinateProofObligations_of_greedy
    (woflanGreedyCoordinateProofObligations_of_basisCover hCover)

theorem woflanCoordinateProofObligations_of_noPredecessorGreedy
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateProofObligations W) :
    WoflanCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyBasisCover
    hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_cover⟩

theorem woflanCoordinateProofObligations_of_noPredecessorGreedy_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    WoflanCoordinateProofObligations W :=
  woflanCoordinateProofObligations_of_noPredecessorGreedy
    (woflanNoPredecessorGreedyCoordinateProofObligations_of_basisCover
      hCover)

theorem woflanCoordinateProofObligations_of_noPredecessorGreedy_lengthNormalizedBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    WoflanCoordinateProofObligations W :=
  woflanCoordinateProofObligations_of_noPredecessorGreedy
    (woflanNoPredecessorGreedyCoordinateProofObligations_of_lengthNormalizedBasisCover
      hCover)

end Petri
end Pm4Lean
