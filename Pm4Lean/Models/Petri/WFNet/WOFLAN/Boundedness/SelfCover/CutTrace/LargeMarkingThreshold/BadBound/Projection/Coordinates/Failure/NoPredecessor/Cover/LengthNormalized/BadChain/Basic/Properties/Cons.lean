import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Definition

namespace Pm4Lean
namespace Petri

theorem length_eq_head_of_lengthNormalizedBadCoverChain_cons
    {W : WFNet} {coords : List Nat} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W (coords :: coordinates)) :
    coords.length = W.net.places.length :=
  hChain.1

theorem not_natListDominatedBy_head_of_lengthNormalizedBadCoverChain_cons
    {W : WFNet} {coords : List Nat} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W (coords :: coordinates)) :
    ¬ NatListDominatedBy coords coordinates :=
  hChain.2.1

theorem natListBasisHasGreaterCoordinateWitness_head_of_lengthNormalizedBadCoverChain_cons
    {W : WFNet} {coords : List Nat} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W (coords :: coordinates)) :
    NatListBasisHasGreaterCoordinateWitness coords coordinates :=
  hChain.2.2.1

theorem lengthNormalizedBadCoverChain_tail_of_cons
    {W : WFNet} {coords : List Nat} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W (coords :: coordinates)) :
    LengthNormalizedBadCoverChain W coordinates :=
  hChain.2.2.2

end Petri
end Pm4Lean
