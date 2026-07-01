import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Definitions.Public

namespace Pm4Lean
namespace Petri

/--
The sharpened coordinate obligation that the Dickson/wqo layer should prove.
It is enough to dominate the greedy coordinate basis of every covered sample
list; the generic greedy-basis cover theorem then covers all predecessor-free
sample coordinates.
-/
structure WoflanGreedyCoordinateProofObligations (W : WFNet) : Prop where
  large_covered_prefix_cut_greedy_coordinate_basis_cover :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W

/--
The predecessor-free greedy-coordinate target.  This is tighter than
`WoflanGreedyCoordinateProofObligations`: the greedy basis is built only from
samples without a comparable raw prefix-cut predecessor, exactly the samples
that the coordinate-cover obligation must dominate.
-/
structure WoflanNoPredecessorGreedyCoordinateProofObligations
    (W : WFNet) : Prop where
  large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_cover :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W

end Petri
end Pm4Lean
