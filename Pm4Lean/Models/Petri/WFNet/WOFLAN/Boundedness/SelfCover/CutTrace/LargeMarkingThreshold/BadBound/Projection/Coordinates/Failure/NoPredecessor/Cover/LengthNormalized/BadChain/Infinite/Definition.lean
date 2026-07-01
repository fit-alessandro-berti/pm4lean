import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic

namespace Pm4Lean
namespace Petri

def LengthNormalizedBadCoverChainSequence (W : WFNet)
    (f : Nat → List Nat) : Prop :=
  (∀ i : Nat, (f i).length = W.net.places.length) ∧
    ∀ prefixLength : Nat,
      LengthNormalizedBadCoverChain W ((List.range prefixLength).map f)

def LengthNormalizedBadCoverChainAppendExtension (W : WFNet) : Prop :=
  ∀ coordinates : List (List Nat),
    LengthNormalizedBadCoverChain W coordinates →
      ∃ coords : List Nat,
        coords.length = W.net.places.length ∧
          ∀ lower : List Nat, lower ∈ coordinates → ¬ NatListLe lower coords

def LengthNormalizedBadCoverChainPrependExtension (W : WFNet) : Prop :=
  ∀ coordinates : List (List Nat),
    LengthNormalizedBadCoverChain W coordinates →
      ∃ coords : List Nat,
        LengthNormalizedBadCoverChain W (coords :: coordinates)

end Petri
end Pm4Lean
