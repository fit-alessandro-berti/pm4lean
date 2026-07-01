import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Properties.Cons

namespace Pm4Lean
namespace Petri

theorem length_eq_of_mem_lengthNormalizedBadCoverChain
    {W : WFNet} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates) :
    ∀ coords : List Nat, coords ∈ coordinates →
      coords.length = W.net.places.length := by
  induction coordinates with
  | nil =>
      intro coords hMem
      cases hMem
  | cons head tail ih =>
      intro coords hMem
      obtain ⟨hHeadLength, _hHeadNotDominated, _hHeadWitness,
        hTailChain⟩ := hChain
      cases hMem with
      | head =>
          exact hHeadLength
      | tail _ hTailMem =>
          exact ih hTailChain coords hTailMem

end Petri
end Pm4Lean
