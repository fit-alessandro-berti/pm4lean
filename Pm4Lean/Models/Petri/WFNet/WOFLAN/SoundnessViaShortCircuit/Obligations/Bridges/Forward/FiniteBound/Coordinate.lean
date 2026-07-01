import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.FiniteBound.Records

namespace Pm4Lean
namespace Petri

theorem woflanCoordinateProofObligations_of_greedy_finiteBound
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_greedyFiniteBoundBasis
    hObligations.large_covered_prefix_cut_greedy_coordinate_finite_bound_basis⟩

theorem woflanCoordinateProofObligations_of_greedy_finiteBoundBasis
    {W : WFNet}
    (hBasis : HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    WoflanCoordinateProofObligations W :=
  woflanCoordinateProofObligations_of_greedy_finiteBound
    (woflanGreedyCoordinateFiniteBoundProofObligations_of_basis hBasis)

theorem woflanCoordinateProofObligations_of_noPredecessorGreedy_finiteBound
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_noPredecessorGreedyFiniteBoundBasis
    hObligations.large_covered_prefix_cut_no_predecessor_greedy_coordinate_finite_bound_basis⟩

theorem woflanCoordinateProofObligations_of_noPredecessorGreedy_finiteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    WoflanCoordinateProofObligations W :=
  woflanCoordinateProofObligations_of_noPredecessorGreedy_finiteBound
    (woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_basis
      hBasis)

end Petri
end Pm4Lean
