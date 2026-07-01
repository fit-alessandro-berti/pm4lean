import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward

namespace Pm4Lean
namespace Petri

theorem woflanCoordinateProofObligations_of_bound
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    WoflanCoordinateProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover_of_bound
    hObligations.large_covered_prefix_cut_no_predecessor_bound⟩

theorem woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_woflan
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound
    hObligations.large_covered_prefix_cut_no_predecessor_bound⟩

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_woflan
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  ⟨(hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateBasisCover).1
    hObligations.large_covered_prefix_cut_no_predecessor_bound⟩

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_woflan
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  ⟨(hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateFiniteBoundBasis).1
    hObligations.large_covered_prefix_cut_no_predecessor_bound⟩

end Petri
end Pm4Lean
