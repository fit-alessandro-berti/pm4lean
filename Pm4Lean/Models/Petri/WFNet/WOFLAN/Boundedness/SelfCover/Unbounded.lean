import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Sequence

namespace Pm4Lean
namespace Petri

theorem arbitrarilyLargeFiringSequenceMarking_of_not_original_bounded
    {W : WFNet}
    (hNotBounded : ¬ TokenBoundedReachableOriginal W) :
    ArbitrarilyLargeFiringSequenceMarking W := by
  intro k
  obtain ⟨M, hReach, p, hGt⟩ :=
    (not_bounded_iff_forall_bound_reachable_gt
      (N := W.net) (M₀ := W.initial)).1 hNotBounded k
  obtain ⟨ts, hSeq⟩ := Reachable.exists_firingSequence hReach
  exact ⟨ts, M, hSeq, p, hGt⟩

theorem not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking
    {W : WFNet}
    (hLarge : ArbitrarilyLargeFiringSequenceMarking W) :
    ¬ TokenBoundedReachableOriginal W := by
  apply (not_bounded_iff_forall_bound_reachable_gt
    (N := W.net) (M₀ := W.initial)).2
  intro k
  obtain ⟨ts, M, hSeq, p, hGt⟩ := hLarge k
  exact ⟨M, Reachable.of_firingSequence hSeq, p, hGt⟩

theorem not_original_bounded_iff_arbitrarilyLargeFiringSequenceMarking
    {W : WFNet} :
    ¬ TokenBoundedReachableOriginal W ↔
      ArbitrarilyLargeFiringSequenceMarking W :=
  ⟨arbitrarilyLargeFiringSequenceMarking_of_not_original_bounded,
    not_original_bounded_of_arbitrarilyLargeFiringSequenceMarking⟩

theorem unboundedOriginalProducesFiringSequenceSelfCover_of_largeSequences
    {W : WFNet}
    (hExtract : LargeSequencesProduceFiringSequenceSelfCover W) :
    UnboundedOriginalProducesFiringSequenceSelfCover W := by
  intro hNotBounded
  exact hExtract
    (arbitrarilyLargeFiringSequenceMarking_of_not_original_bounded
      hNotBounded)

end Petri
end Pm4Lean
