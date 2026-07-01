import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Definitions.Cover.Raw

namespace Pm4Lean
namespace Petri

def HasLargeCoveredPrefixCutNoPredecessorCoordinateDominatingCover
    (W : WFNet) : Prop :=
  ∃ coordinates : List (List Nat),
    LargeCoveredPrefixCutSamplesWithoutPredecessorCoordinateListsDominatedBy
      W coordinates

def HasLargeCoveredPrefixCutGreedyCoordinateBasisCover
    (W : WFNet) : Prop :=
  ∃ coordinates : List (List Nat),
    LargeCoveredPrefixCutGreedyCoordinateBasesDominatedBy W coordinates

def HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasisCover
    (W : WFNet) : Prop :=
  ∃ coordinates : List (List Nat),
    LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
      W coordinates

def HasLargeCoveredPrefixCutNoPredecessorGreedyCoordinateLengthNormalizedBasisCover
    (W : WFNet) : Prop :=
  ∃ coordinates : List (List Nat),
    (∀ coords : List Nat, coords ∈ coordinates →
      coords.length = W.net.places.length) ∧
      LargeCoveredPrefixCutNoPredecessorGreedyCoordinateBasesDominatedBy
        W coordinates

end Petri
end Pm4Lean
