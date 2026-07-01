import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Definitions.Bound

namespace Pm4Lean
namespace Petri

/--
A finite-basis variant of the predecessor-free scalar-bound target.
-/
structure WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations
    (W : WFNet) : Prop where
  large_covered_prefix_cut_no_predecessor_greedy_coordinate_finite_bound_basis :
    HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis W

/--
A finite-basis variant of the scalar-bound target.  This is useful for proof
steps that naturally produce one local bound per finite case before collapsing
them with `NatListMax`.
-/
structure WoflanGreedyCoordinateFiniteBoundProofObligations (W : WFNet) : Prop where
  large_covered_prefix_cut_greedy_coordinate_finite_bound_basis :
    HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W

end Petri
end Pm4Lean
