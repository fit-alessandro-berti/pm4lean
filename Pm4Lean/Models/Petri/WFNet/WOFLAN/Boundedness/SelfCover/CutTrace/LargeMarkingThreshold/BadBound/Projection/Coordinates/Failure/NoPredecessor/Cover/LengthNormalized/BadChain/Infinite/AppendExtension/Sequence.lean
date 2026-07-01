import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite.AppendExtension.Prefix

namespace Pm4Lean
namespace Petri

noncomputable def lengthNormalizedBadCoverChainAppendSequence
    (W : WFNet)
    (hExtend : LengthNormalizedBadCoverChainAppendExtension W)
    (i : Nat) : List Nat :=
  Classical.choose
    (hExtend
      (lengthNormalizedBadCoverChainAppendPrefix W hExtend i).1
      (lengthNormalizedBadCoverChainAppendPrefix W hExtend i).2)

theorem map_range_lengthNormalizedBadCoverChainAppendSequence_eq_prefix
    {W : WFNet}
    (hExtend : LengthNormalizedBadCoverChainAppendExtension W)
    (n : Nat) :
    (List.range n).map
        (lengthNormalizedBadCoverChainAppendSequence W hExtend) =
      (lengthNormalizedBadCoverChainAppendPrefix W hExtend n).1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, ih]
      simp [lengthNormalizedBadCoverChainAppendPrefix,
        lengthNormalizedBadCoverChainAppendSequence]

theorem exists_lengthNormalizedBadCoverChainSequence_of_appendExtension
    {W : WFNet}
    (hExtend : LengthNormalizedBadCoverChainAppendExtension W) :
    ∃ f : Nat → List Nat, LengthNormalizedBadCoverChainSequence W f := by
  let f := lengthNormalizedBadCoverChainAppendSequence W hExtend
  refine ⟨f, ?_, ?_⟩
  · intro i
    exact
      (Classical.choose_spec
        (hExtend
          (lengthNormalizedBadCoverChainAppendPrefix W hExtend i).1
          (lengthNormalizedBadCoverChainAppendPrefix W hExtend i).2)).1
  · intro prefixLength
    rw [map_range_lengthNormalizedBadCoverChainAppendSequence_eq_prefix
      hExtend prefixLength]
    exact (lengthNormalizedBadCoverChainAppendPrefix W hExtend prefixLength).2

end Petri
end Pm4Lean
