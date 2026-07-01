import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Properties

namespace Pm4Lean
namespace Petri

theorem lengthNormalizedBadCoverChain_of_pairwise_not_natListLe
    {W : WFNet} {coordinates : List (List Nat)}
    (hLength :
      ∀ coords : List Nat, coords ∈ coordinates →
        coords.length = W.net.places.length)
    (hPairwise :
      List.Pairwise (fun xs ys => ¬ NatListLe xs ys) coordinates) :
    LengthNormalizedBadCoverChain W coordinates := by
  induction coordinates with
  | nil =>
      trivial
  | cons head tail ih =>
      rw [List.pairwise_cons] at hPairwise
      have hTailLength :
          ∀ coords : List Nat, coords ∈ tail →
            coords.length = W.net.places.length := by
        intro coords hCoordsMem
        exact hLength coords (List.Mem.tail head hCoordsMem)
      have hHeadNotDominated : ¬ NatListDominatedBy head tail := by
        intro hDominated
        obtain ⟨upper, hUpperMem, hLe⟩ := hDominated
        exact hPairwise.1 upper hUpperMem hLe
      exact ⟨hLength head (List.Mem.head tail),
        hHeadNotDominated,
        natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
          (hLength head (List.Mem.head tail))
          hTailLength
          hHeadNotDominated,
        ih hTailLength hPairwise.2⟩

theorem lengthNormalizedBadCoverChain_of_not_containsNatListLePair
    {W : WFNet} {coordinates : List (List Nat)}
    (hLength :
      ∀ coords : List Nat, coords ∈ coordinates →
        coords.length = W.net.places.length)
    (hNoPair : ¬ ContainsNatListLePair coordinates) :
    LengthNormalizedBadCoverChain W coordinates :=
  lengthNormalizedBadCoverChain_of_pairwise_not_natListLe
    hLength
    (not_containsNatListLePair_iff_pairwise_not_natListLe.mp hNoPair)

end Petri
end Pm4Lean
