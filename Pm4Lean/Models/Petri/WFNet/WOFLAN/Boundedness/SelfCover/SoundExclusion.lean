import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.Unbounded

namespace Pm4Lean
namespace Petri

theorem final_plus_difference_ne_final_of_strict_cover
    {W : WFNet} {M M' : W.Marking}
    (hLe : M ≤ M') (hNe : M ≠ M') :
    W.final + (M' - M) ≠ W.final := by
  intro hEq
  obtain ⟨p, hLt⟩ := Marking.exists_lt_of_le_ne hLe hNe
  have hPositive : 0 < M' p - M p := Nat.sub_pos_of_lt hLt
  have hStrict :
      W.final p < (W.final + (M' - M)) p := by
    exact Nat.lt_add_of_pos_right hPositive
  rw [hEq] at hStrict
  exact Nat.lt_irrefl (W.final p) hStrict

theorem sound_excludes_reachable_self_cover
    {W : WFNet} (hSound : Sound W) :
    ¬ ReachableSelfCover W := by
  intro hSelfCover
  obtain ⟨M, M', hReachInitialM, hReachMM', hLe, hNe⟩ := hSelfCover
  let K : W.Marking := M' - M
  have hMAddK : M + K = M' := by
    simpa [K] using Marking.add_sub_of_le hLe
  have hComplete : Reachable W.net M W.final :=
    hSound.1 M hReachInitialM
  have hCompleteWithExtra :
      Reachable W.net (M + K) (W.final + K) :=
    Reachable.add_right hComplete K
  have hM'CompleteWithExtra :
      Reachable W.net M' (W.final + K) := by
    simpa [hMAddK] using hCompleteWithExtra
  have hReachFinalWithExtra :
      Reachable W.net W.initial (W.final + K) :=
    Reachable.trans
      (Reachable.trans hReachInitialM hReachMM')
      hM'CompleteWithExtra
  have hFinalCovered : W.final ≤ W.final + K := by
    intro p
    exact Nat.le_add_right (W.final p) (K p)
  have hProperEq : W.final + K = W.final :=
    hSound.2.1 (W.final + K) hReachFinalWithExtra hFinalCovered
  exact final_plus_difference_ne_final_of_strict_cover
    (W := W) hLe hNe (by simpa [K] using hProperEq)

theorem sound_excludes_firingSequence_self_cover
    {W : WFNet} (hSound : Sound W) :
    ¬ FiringSequenceSelfCover W := by
  intro hCover
  exact sound_excludes_reachable_self_cover hSound
    (reachableSelfCover_of_firingSequenceSelfCover hCover)

theorem original_bounded_of_sound_and_self_cover_extraction
    {W : WFNet}
    (hExtract : UnboundedOriginalProducesSelfCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W := by
  classical
  exact Classical.byContradiction (fun hNotBounded =>
    sound_excludes_reachable_self_cover hSound (hExtract hNotBounded))

theorem original_bounded_of_sound_and_firingSequence_self_cover_extraction
    {W : WFNet}
    (hExtract : UnboundedOriginalProducesFiringSequenceSelfCover W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_self_cover_extraction
    (unboundedOriginalProducesSelfCover_of_firingSequence hExtract)
    hSound

end Petri
end Pm4Lean
