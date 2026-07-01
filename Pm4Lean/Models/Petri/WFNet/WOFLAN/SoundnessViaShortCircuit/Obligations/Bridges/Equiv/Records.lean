import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Bridges.Equiv.FromPublic

namespace Pm4Lean
namespace Petri

theorem woflanProofObligations_iff_coordinate
    {W : WFNet} :
    WoflanProofObligations W ↔ WoflanCoordinateProofObligations W :=
  ⟨woflanCoordinateProofObligations_of_bound,
    woflanProofObligations_of_coordinate⟩

theorem woflanProofObligations_iff_noPredecessorGreedyCoordinateBound
    {W : WFNet} :
    WoflanProofObligations W ↔
      WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  ⟨woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_woflan,
    woflanProofObligations_of_noPredecessorGreedy_bound⟩

theorem woflanProofObligations_iff_noPredecessorGreedyCoordinateBasisCover
    {W : WFNet} :
    WoflanProofObligations W ↔
      WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  ⟨woflanNoPredecessorGreedyCoordinateProofObligations_of_woflan,
    woflanProofObligations_of_noPredecessorGreedy⟩

theorem woflanProofObligations_iff_noPredecessorGreedyCoordinateFiniteBound
    {W : WFNet} :
    WoflanProofObligations W ↔
      WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  ⟨woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_woflan,
    woflanProofObligations_of_noPredecessorGreedy_finiteBound⟩

end Petri
end Pm4Lean
