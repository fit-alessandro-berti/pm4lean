import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Definitions.Greedy

namespace Pm4Lean
namespace Petri

/--
An even smaller scalar-bound target for the Dickson/wqo layer: prove one
natural number bounds every coordinate of every vector retained by every
covered-sample greedy basis.
-/
structure WoflanGreedyCoordinateBoundProofObligations (W : WFNet) : Prop where
  large_covered_prefix_cut_greedy_coordinate_basis_bound :
    HasLargeCoveredPrefixCutGreedyCoordinateBasisBound W

/--
A scalar-bound version of the predecessor-free greedy-coordinate target.
-/
structure WoflanNoPredecessorGreedyCoordinateBoundProofObligations
    (W : WFNet) : Prop where
  large_covered_prefix_cut_no_predecessor_greedy_coordinate_basis_bound :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisBound W

end Petri
end Pm4Lean
