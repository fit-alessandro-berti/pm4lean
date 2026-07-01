import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Filtered.Cover.LengthNormalized.Failure
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Existence.Construction.Prepend
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite.Contradiction

namespace Pm4Lean
namespace Petri

theorem exists_lengthNormalizedBadCoverChain_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W)
    (n : Nat) :
    ∃ coordinates : List (List Nat),
      coordinates.length = n ∧
        LengthNormalizedBadCoverChain W coordinates :=
  exists_lengthNormalizedBadCoverChain_of_not_length_normalized_cover
    hNotCover n

theorem arbitrarilyLongLengthNormalizedBadCoverChains_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    ArbitrarilyLongLengthNormalizedBadCoverChains W :=
  arbitrarilyLongLengthNormalizedBadCoverChains_of_not_length_normalized_cover
    hNotCover

theorem lengthNormalizedBadCoverChainPrependExtension_of_not_noPredecessorGreedyCoordinateLengthNormalizedBasisCover
    {W : WFNet}
    (hNotCover :
      ¬ HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
        W) :
    LengthNormalizedBadCoverChainPrependExtension W :=
  lengthNormalizedBadCoverChainPrependExtension_of_not_length_normalized_cover
    hNotCover

theorem not_noPredecessorLengthNormalizedBadCoverChainAppendExtension
    {W : WFNet} :
    ¬ LengthNormalizedBadCoverChainAppendExtension W :=
  not_lengthNormalizedBadCoverChainAppendExtension

theorem not_exists_noPredecessorLengthNormalizedBadCoverChainSequence
    {W : WFNet} :
    ¬ ∃ f : Nat → List Nat, LengthNormalizedBadCoverChainSequence W f :=
  not_exists_lengthNormalizedBadCoverChainSequence

theorem lengthNormalizedBadCoverChain_iff_not_noPredecessorNatListLePair
    {W : WFNet} {coordinates : List (List Nat)} :
    LengthNormalizedBadCoverChain W coordinates ↔
      (∀ coords : List Nat, coords ∈ coordinates →
        coords.length = W.net.places.length) ∧
        ¬ ContainsNatListLePair coordinates :=
  lengthNormalizedBadCoverChain_iff_not_containsNatListLePair

end Petri
end Pm4Lean
