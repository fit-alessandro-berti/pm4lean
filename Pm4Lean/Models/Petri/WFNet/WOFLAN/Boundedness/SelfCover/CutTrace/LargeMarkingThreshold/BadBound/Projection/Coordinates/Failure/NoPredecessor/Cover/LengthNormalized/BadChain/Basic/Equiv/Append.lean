import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Equiv.Pairwise

namespace Pm4Lean
namespace Petri

theorem lengthNormalizedBadCoverChain_append_singleton_iff
    {W : WFNet} {coordinates : List (List Nat)} {coords : List Nat} :
    LengthNormalizedBadCoverChain W (coordinates ++ [coords]) ↔
      LengthNormalizedBadCoverChain W coordinates ∧
        coords.length = W.net.places.length ∧
        ∀ lower : List Nat, lower ∈ coordinates → ¬ NatListLe lower coords := by
  constructor
  · intro hChain
    have hPairwise :
        List.Pairwise (fun xs ys => ¬ NatListLe xs ys)
          (coordinates ++ [coords]) :=
      pairwise_not_natListLe_of_lengthNormalizedBadCoverChain hChain
    rw [List.pairwise_append] at hPairwise
    exact
      ⟨lengthNormalizedBadCoverChain_of_pairwise_not_natListLe
          (fun lower hLowerMem =>
            length_eq_of_mem_lengthNormalizedBadCoverChain hChain lower
              (List.mem_append_left [coords] hLowerMem))
          hPairwise.1,
        length_eq_of_mem_lengthNormalizedBadCoverChain hChain coords
          (by simp),
        fun lower hLowerMem =>
          hPairwise.2.2 lower hLowerMem coords (by simp)⟩
  · intro h
    obtain ⟨hChain, hCoordsLength, hNoLeLast⟩ := h
    apply lengthNormalizedBadCoverChain_of_pairwise_not_natListLe
    · intro lower hLowerMem
      rw [List.mem_append] at hLowerMem
      cases hLowerMem with
      | inl hMem =>
          exact length_eq_of_mem_lengthNormalizedBadCoverChain hChain lower hMem
      | inr hMem =>
          simp at hMem
          subst lower
          exact hCoordsLength
    · rw [List.pairwise_append]
      exact
        ⟨pairwise_not_natListLe_of_lengthNormalizedBadCoverChain hChain,
          by simp,
          fun lower hLowerMem upper hUpperMem => by
            simp at hUpperMem
            subst upper
            exact hNoLeLast lower hLowerMem⟩

end Petri
end Pm4Lean
