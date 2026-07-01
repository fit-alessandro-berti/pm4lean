import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Definitions

namespace Pm4Lean
namespace Petri

theorem woflanGreedyCoordinateProofObligations_of_basisCover
    {W : WFNet}
    (hCover : HasLargeCoveredPrefixCutGreedyCoordinateBasisCover W) :
    WoflanGreedyCoordinateProofObligations W :=
  ⟨hCover⟩

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_basisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  ⟨hCover⟩

theorem woflanNoPredecessorGreedyCoordinateProofObligations_of_lengthNormalizedBasisCover
    {W : WFNet}
    (hCover :
      HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    WoflanNoPredecessorGreedyCoordinateProofObligations W :=
  woflanNoPredecessorGreedyCoordinateProofObligations_of_basisCover
    (hasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover_of_length_normalized
      hCover)

end Petri
end Pm4Lean
