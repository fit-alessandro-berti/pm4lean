import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Forward.FiniteBound.Coordinate

namespace Pm4Lean
namespace Petri

theorem woflanProofObligations_of_noPredecessorGreedy_finiteBound
    {W : WFNet}
    (hObligations :
      WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_noPredecessorGreedy_finiteBound
      hObligations)

theorem woflanProofObligations_of_noPredecessorGreedy_finiteBoundBasis
    {W : WFNet}
    (hBasis :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateFiniteBoundBasis
        W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_noPredecessorGreedy_finiteBoundBasis
      hBasis)

theorem woflanProofObligations_of_greedy_finiteBound
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateFiniteBoundProofObligations W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_greedy_finiteBound
      hObligations)

theorem woflanProofObligations_of_greedy_finiteBoundBasis
    {W : WFNet}
    (hBasis : HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    WoflanProofObligations W :=
  woflanProofObligations_of_coordinate
    (woflanCoordinateProofObligations_of_greedy_finiteBoundBasis
      hBasis)

end Petri
end Pm4Lean
