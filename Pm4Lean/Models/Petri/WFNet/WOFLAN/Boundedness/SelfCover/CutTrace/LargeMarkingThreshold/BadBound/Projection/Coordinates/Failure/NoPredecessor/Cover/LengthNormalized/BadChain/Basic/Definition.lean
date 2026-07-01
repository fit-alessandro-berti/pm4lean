import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.Base

namespace Pm4Lean
namespace Petri

def LengthNormalizedBadCoverChain (W : WFNet) :
    List (List Nat) → Prop
  | [] => True
  | coords :: coordinates =>
      coords.length = W.net.places.length ∧
        ¬ NatListDominatedBy coords coordinates ∧
        NatListBasisHasGreaterCoordinateWitness coords coordinates ∧
        LengthNormalizedBadCoverChain W coordinates

def ArbitrarilyLongLengthNormalizedBadCoverChains (W : WFNet) : Prop :=
  ∀ n : Nat,
    ∃ coordinates : List (List Nat),
      coordinates.length = n ∧
        LengthNormalizedBadCoverChain W coordinates

end Petri
end Pm4Lean
