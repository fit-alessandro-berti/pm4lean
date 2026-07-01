import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Bound.Negative

namespace Pm4Lean
namespace Petri

theorem woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_woflan
    (woflanProofObligations_of_original_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_live_and_bounded_shortCircuit
    {W : WFNet}
    (hLiveBounded :
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial) :
    WoflanNoPredecessorGreedyCoordinateBoundProofObligations W :=
  woflanNoPredecessorGreedyCoordinateBoundProofObligations_of_shortCircuit_bounded
    hLiveBounded.2

end Petri
end Pm4Lean
