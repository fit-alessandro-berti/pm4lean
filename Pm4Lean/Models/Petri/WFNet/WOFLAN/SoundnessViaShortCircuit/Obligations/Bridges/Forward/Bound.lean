import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.Cover

namespace Pm4Lean
namespace Petri

theorem woflanGreedyCoordinateProofObligations_of_bound
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateBoundProofObligations W) :
    WoflanGreedyCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutGreedyCoordinateBasisCover_of_bound
    hObligations.large_covered_prefix_cut_greedy_coordinate_basis_bound⟩

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_bound
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
    hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_bound⟩

theorem noPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_boundObligations
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
      W :=
  hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_bound
    hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_bound

theorem woflanProofObligations_of_greedy_bound
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateBoundProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_greedy
    (woflanGreedyCoordinateProofObligations_of_bound hObligations)

theorem woflanProofObligations_of_noPredecessorGreedy_bound
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_noPredecessorGreedy
    (woflanNoPredecessorGreedyCoordinateProofObligations_of_bound
      hObligations)

end Petri
end Pm4Lean
