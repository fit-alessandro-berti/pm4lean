import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.CutTrace.LargeMarkingThreshold.BadBound.Projection.Coordinates.Failure.NoPredecessor.Cover.LengthNormalized.BadChain.Infinite.AppendExtension
import Pm4Lean.Util.NatListOrder.GoodPair.Infinite

namespace Pm4Lean
namespace Petri

theorem exists_not_lengthNormalizedBadCoverChain_map_range_of_forall_length_sequence
    {W : WFNet} {f : Nat → List Nat}
    (hLength : ∀ i : Nat, (f i).length = W.net.places.length) :
    ∃ prefixLength : Nat,
      ¬ LengthNormalizedBadCoverChain W ((List.range prefixLength).map f) := by
  obtain ⟨prefixLength, hPair⟩ :=
    exists_containsNatListLePair_map_range_of_forall_length_sequence
      W.net.places.length f hLength
  exact ⟨prefixLength, fun hChain =>
    not_containsNatListLePair_of_lengthNormalizedBadCoverChain hChain hPair⟩

theorem not_forall_lengthNormalizedBadCoverChain_map_range_of_forall_length_sequence
    {W : WFNet} {f : Nat → List Nat}
    (hLength : ∀ i : Nat, (f i).length = W.net.places.length) :
    ¬ ∀ prefixLength : Nat,
      LengthNormalizedBadCoverChain W ((List.range prefixLength).map f) := by
  intro hAll
  obtain ⟨prefixLength, hNotChain⟩ :=
    exists_not_lengthNormalizedBadCoverChain_map_range_of_forall_length_sequence
      hLength
  exact hNotChain (hAll prefixLength)

theorem not_lengthNormalizedBadCoverChainSequence
    {W : WFNet} {f : Nat → List Nat} :
    ¬ LengthNormalizedBadCoverChainSequence W f := by
  intro hSequence
  exact not_forall_lengthNormalizedBadCoverChain_map_range_of_forall_length_sequence
    hSequence.1 hSequence.2

theorem not_exists_lengthNormalizedBadCoverChainSequence
    {W : WFNet} :
    ¬ ∃ f : Nat → List Nat, LengthNormalizedBadCoverChainSequence W f := by
  intro hExists
  obtain ⟨f, hSequence⟩ := hExists
  exact not_lengthNormalizedBadCoverChainSequence hSequence

theorem not_lengthNormalizedBadCoverChainAppendExtension
    {W : WFNet} :
    ¬ LengthNormalizedBadCoverChainAppendExtension W := by
  intro hExtend
  obtain ⟨f, hSequence⟩ :=
    exists_lengthNormalizedBadCoverChainSequence_of_appendExtension hExtend
  exact not_lengthNormalizedBadCoverChainSequence hSequence

end Petri
end Pm4Lean
