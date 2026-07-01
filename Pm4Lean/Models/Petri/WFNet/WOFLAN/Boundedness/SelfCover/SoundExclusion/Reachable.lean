import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover.SoundExclusion.Final

namespace Pm4Lean
namespace Petri

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

end Petri
end Pm4Lean
