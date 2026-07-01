import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Sufficient.Bound

namespace Pm4Lean
namespace Petri

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateBasisBound
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W :=
  ⟨hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound,
    hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisBound⟩

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateFiniteBoundBasis
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis W := by
  constructor
  · intro hBound
    exact
      hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis_of_bound
        (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound
          hBound)
  · exact hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyFiniteBoundBasis

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateBasisCover
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W := by
  constructor
  · intro hBound
    exact
      hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_bound
        (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound
          hBound)
  · exact hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisCover

theorem hasLargeCoveredPrefixCutNoPredecessorBound_iff_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet} :
    HasLargeCoveredPrefixCutNoPredecessorBound W ↔
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W := by
  constructor
  · intro hBound
    exact
      hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover_of_bound
        (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound_of_bound
          hBound)
  · intro hCover
    exact
      hasLargeCoveredPrefixCutNoPredecessorBound_of_noPredecessorGreedyBasisCover
        (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized
          hCover)

end Petri
end Pm4Lean
