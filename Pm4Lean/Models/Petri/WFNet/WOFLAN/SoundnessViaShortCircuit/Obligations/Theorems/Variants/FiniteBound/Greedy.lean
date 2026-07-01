import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.FiniteBound.NoPredecessorBasis

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_woflan_greedy_coordinate_finite_bound_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateFiniteBoundProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_greedy_finiteBound hObligations)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_greedy_coordinate_finite_bound_obligations
    {W : WFNet}
    (hObligations : WoflanGreedyCoordinateFiniteBoundProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_greedy_finiteBound hObligations)

theorem original_bounded_of_sound_and_greedy_coordinate_finite_bound_basis
    {W : WFNet}
    (hBasis : HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_greedy_finiteBoundBasis hBasis)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_greedy_coordinate_finite_bound_basis
    {W : WFNet}
    (hBasis : HasLargeCoveredPrefixCutGreedyCoordinateFiniteBoundBasis W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_greedy_finiteBoundBasis hBasis)

end Petri
end Pm4Lean
