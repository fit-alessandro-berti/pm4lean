import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite.Definition

namespace Pm4Lean
namespace Petri

noncomputable def lengthNormalizedBadCoverChainAppendPrefix
    (W : WFNet)
    (hExtend : LengthNormalizedBadCoverChainAppendExtension W) :
    Nat → {coordinates : List (List Nat) //
      LengthNormalizedBadCoverChain W coordinates}
  | 0 => ⟨[], trivial⟩
  | n + 1 =>
      let previous :=
        lengthNormalizedBadCoverChainAppendPrefix W hExtend n
      let next := Classical.choose (hExtend previous.1 previous.2)
      let hNext := Classical.choose_spec (hExtend previous.1 previous.2)
      ⟨previous.1 ++ [next],
        lengthNormalizedBadCoverChain_append_singleton_iff.mpr
          ⟨previous.2, hNext.1, hNext.2⟩⟩

end Petri
end Pm4Lean
