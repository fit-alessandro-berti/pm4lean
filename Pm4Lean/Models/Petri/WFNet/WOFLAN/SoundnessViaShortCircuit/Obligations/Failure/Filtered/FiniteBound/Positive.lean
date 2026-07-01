import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.FiniteBound.Unbounded

namespace Pm4Lean
namespace Petri

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_woflan
    (woflanProofObligations_of_original_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_live_and_bounded_shortCircuit
    {W : WFNet}
    (hLiveBounded :
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateFiniteBoundProofObligations_of_shortCircuit_bounded
    hLiveBounded.2

end Petri
end Pm4Lean
