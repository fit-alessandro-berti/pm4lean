import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite.Definition
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Base.Witness.Extension

namespace Pm4Lean
namespace Petri

theorem lengthNormalizedBadCoverChainPrependExtension_of_not_length_normalized_cover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    LengthNormalizedBadCoverChainPrependExtension W := by
  intro coordinates hChain
  have hCoordinatesLength :
      ∀ upper : List Nat, upper ∈ coordinates →
        upper.length = W.net.places.length :=
    length_eq_of_mem_lengthNormalizedBadCoverChain hChain
  obtain ⟨ts, Mend, hSeq, samples, hCovered, coords, hCoordsMem,
      hCoordsLength, _hNotMem, hNotDominated, hWitness,
      _hExtendedLength⟩ :=
    exists_retained_noPredecessorGreedyCoordinate_extension_of_not_length_normalized_cover
      hNotCover coordinates hCoordinatesLength
  exact ⟨coords, ⟨hCoordsLength, hNotDominated, hWitness, hChain⟩⟩

end Petri
end Pm4Lean
