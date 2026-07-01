import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Basic.Properties.Length

namespace Pm4Lean
namespace Petri

theorem nodup_of_lengthNormalizedBadCoverChain
    {W : WFNet} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates) :
    coordinates.Nodup := by
  induction coordinates with
  | nil =>
      exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨_hHeadLength, hHeadNotDominated, _hHeadWitness,
        hTailChain⟩ := hChain
      exact List.nodup_cons.mpr
        ⟨not_mem_of_not_natListDominatedBy hHeadNotDominated,
          ih hTailChain⟩

theorem pairwise_not_natListLe_of_lengthNormalizedBadCoverChain
    {W : WFNet} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates) :
    List.Pairwise (fun xs ys => ¬ NatListLe xs ys) coordinates := by
  induction coordinates with
  | nil =>
      exact List.Pairwise.nil
  | cons head tail ih =>
      obtain ⟨_hHeadLength, hHeadNotDominated, _hHeadWitness,
        hTailChain⟩ := hChain
      exact List.Pairwise.cons
        (fun upper hUpperMem hLe =>
          hHeadNotDominated
            (natListDominatedBy_of_mem_le hUpperMem hLe))
        (ih hTailChain)

theorem not_containsNatListLePair_of_lengthNormalizedBadCoverChain
    {W : WFNet} {coordinates : List (List Nat)}
    (hChain : LengthNormalizedBadCoverChain W coordinates) :
    ¬ ContainsNatListLePair coordinates :=
  not_containsNatListLePair_iff_pairwise_not_natListLe.mpr
    (pairwise_not_natListLe_of_lengthNormalizedBadCoverChain hChain)

end Petri
end Pm4Lean
