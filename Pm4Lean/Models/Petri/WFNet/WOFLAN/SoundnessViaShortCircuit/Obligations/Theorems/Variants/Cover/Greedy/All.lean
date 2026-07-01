import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Theorems.Variants.Cover.Coordinate

namespace Pm4Lean
namespace Petri

theorem original_bounded_of_sound_and_greedy_coordinate_basis_cover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_woflan_obligations
    (woflanProofObligations_of_greedy_basisCover hCover)
    hSound

theorem sound_iff_live_and_bounded_shortCircuit_of_greedy_coordinate_basis_cover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial :=
  sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    (woflanProofObligations_of_greedy_basisCover hCover)

end Petri
end Pm4Lean
