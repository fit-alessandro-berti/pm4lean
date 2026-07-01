import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Finiteness.Escape.Basis

namespace Pm4Lean
namespace Petri

theorem exists_large_coordinate_of_lengthNormalizedBadCoverChain_length_gt
    {W : WFNet} {coordinates : List (List Nat)} {k : Nat}
    (hChain : LengthNormalizedBadCoverChain W coordinates)
    (hLength :
      (NatListsUpTo W.net.places.length k).length <
        coordinates.length) :
    ∃ coords : List Nat, coords ∈ coordinates ∧
      ∃ x : Nat, x ∈ coords ∧ k < x := by
  classical
  exact Classical.byContradiction (fun hNoLarge =>
    let hBound :
        ∀ coords : List Nat, coords ∈ coordinates →
          ∀ x : Nat, x ∈ coords → x ≤ k := by
      intro coords hCoordsMem x hXMem
      by_cases hLe : x ≤ k
      · exact hLe
      · exact False.elim
          (hNoLarge
            ⟨coords, hCoordsMem, x, hXMem, Nat.lt_of_not_ge hLe⟩)
    Nat.not_lt_of_ge
      (length_le_natListsUpTo_length_of_lengthNormalizedBadCoverChain_bounded
        hChain hBound)
      hLength)

end Petri
end Pm4Lean
