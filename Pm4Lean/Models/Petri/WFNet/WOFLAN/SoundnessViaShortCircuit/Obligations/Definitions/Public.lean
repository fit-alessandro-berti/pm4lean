import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover

namespace Pm4Lean
namespace Petri

/--
The remaining proof obligations for the classic WOFLAN theorem

`Sound W ↔ Live (shortCircuit W) W.initial ∧ Bounded (shortCircuit W) W.initial`.

The only remaining field is the uniform finite/Dickson threshold over prefix
cuts: all covered samples without a comparable raw prefix-cut predecessor are
bounded by one natural number.  Any sample above that threshold must therefore
have a predecessor, and the cut-trace and sequence lemmas then turn comparable
cuts into the prefix/loop self-cover excluded by soundness.
-/
structure WoflanProofObligations (W : WFNet) : Prop where
  large_covered_prefix_cut_no_predecessor_bound :
    HasLargeCoveredPrefixCutNoPredecessorBound W

/--
The same WOFLAN obligations, but stated at the finite-coordinate boundary.
This is the preferred target for the remaining Dickson/wqo proof: produce a
finite set of natural-number vectors that dominates every predecessor-free
covered prefix-cut sample.
-/
structure WoflanCoordinateProofObligations (W : WFNet) : Prop where
  large_covered_prefix_cut_no_predecessor_coordinate_cover :
    HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover W

end Petri
end Pm4Lean
