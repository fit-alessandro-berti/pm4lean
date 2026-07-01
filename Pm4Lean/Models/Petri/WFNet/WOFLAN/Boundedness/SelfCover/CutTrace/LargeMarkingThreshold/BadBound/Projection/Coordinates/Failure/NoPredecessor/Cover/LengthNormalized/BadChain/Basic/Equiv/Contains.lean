import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Equiv.Pairwise

namespace Pm4Lean
namespace Petri

theorem lengthNormalizedBadCoverChain_iff_not_containsNatListLePair
    {W : WFNet} {coordinates : List (List Nat)} :
    LengthNormalizedBadCoverChain W coordinates ↔
      (∀ coords : List Nat, coords ∈ coordinates →
        coords.length = W.net.places.length) ∧
        ¬ ContainsNatListLePair coordinates := by
  constructor
  · intro hChain
    exact ⟨length_eq_of_mem_lengthNormalizedBadCoverChain hChain,
      not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain⟩
  · intro h
    exact lengthNormalizedBadCoverChain_of_not_containsNatListLePair
      h.1 h.2

end Petri
end Pm4Lean
