import Pm4Lean.Conversion.POWL2ToSoundWfNet.TargetShape.Core

namespace Pm4Lean
namespace ProcessModel
namespace POWL2ToSoundWfNet

variable {Activity : Type u}

namespace TargetShape

namespace NetEmbedding

noncomputable def mapMarking
    {N₁ N₂ : Petri.Net}
    (mapPlace : N₁.Place → N₂.Place)
    (M : N₁.Marking) : N₂.Marking :=
  by
    classical
    exact fun q =>
      if h : ∃ p : N₁.Place, mapPlace p = q then
        M h.choose
      else
        0

theorem mapMarking_apply
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    (hInj : Function.Injective mapPlace)
    (M : N₁.Marking) (p : N₁.Place) :
    mapMarking mapPlace M (mapPlace p) = M p := by
  classical
  change
    (if h : ∃ p' : N₁.Place, mapPlace p' = mapPlace p then
      M h.choose
    else
      0) = M p
  by_cases h : ∃ p' : N₁.Place, mapPlace p' = mapPlace p
  · have hChosen : h.choose = p :=
      hInj h.choose_spec
    simp [h, hChosen]
  · exact False.elim (h ⟨p, rfl⟩)

theorem mapMarking_zero_of_not_mapped
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    (M : N₁.Marking) (q : N₂.Place)
    (hNotMapped : ¬ ∃ p : N₁.Place, mapPlace p = q) :
    mapMarking mapPlace M q = 0 := by
  classical
  simp [mapMarking, hNotMapped]

theorem mapMarking_singleton
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    (hInj : Function.Injective mapPlace)
    (p : N₁.Place) :
    mapMarking mapPlace (Petri.Marking.singleton p) =
      Petri.Marking.singleton (mapPlace p) := by
  apply Petri.Marking.ext
  intro q
  by_cases hMapped : ∃ p' : N₁.Place, mapPlace p' = q
  · obtain ⟨p', rfl⟩ := hMapped
    rw [mapMarking_apply hInj]
    by_cases hEq : p' = p
    · subst hEq
      simp [Petri.Marking.singleton]
    · have hImageNe : mapPlace p' ≠ mapPlace p := by
        intro hImage
        exact hEq (hInj hImage)
      simp [Petri.Marking.singleton, hEq, hImageNe]
  · rw [mapMarking_zero_of_not_mapped (Petri.Marking.singleton p) q hMapped]
    have hNe : q ≠ mapPlace p := by
      intro hEq
      exact hMapped ⟨p, hEq.symm⟩
    simp [Petri.Marking.singleton, hNe]

theorem enabled_map
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    {mapTransition : N₁.Transition → N₂.Transition}
    (hPlaceInj : Function.Injective mapPlace)
    (hPre :
      ∀ (t : N₁.Transition) (p : N₁.Place),
        N₂.pre (mapTransition t) (mapPlace p) = N₁.pre t p)
    (hPreZero :
      ∀ (t : N₁.Transition) (q : N₂.Place),
        (¬ ∃ p : N₁.Place, mapPlace p = q) →
          N₂.pre (mapTransition t) q = 0)
    {M : N₁.Marking} {t : N₁.Transition}
    (hEnabled : Petri.Enabled N₁ M t) :
    Petri.Enabled N₂ (mapMarking mapPlace M) (mapTransition t) := by
  intro q
  by_cases hMapped : ∃ p : N₁.Place, mapPlace p = q
  · obtain ⟨p, rfl⟩ := hMapped
    rw [hPre, mapMarking_apply hPlaceInj]
    exact hEnabled p
  · rw [hPreZero t q hMapped, mapMarking_zero_of_not_mapped M q hMapped]
    exact Nat.le_refl 0

theorem fire_map
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    {mapTransition : N₁.Transition → N₂.Transition}
    (hPlaceInj : Function.Injective mapPlace)
    (hPre :
      ∀ (t : N₁.Transition) (p : N₁.Place),
        N₂.pre (mapTransition t) (mapPlace p) = N₁.pre t p)
    (hPost :
      ∀ (t : N₁.Transition) (p : N₁.Place),
        N₂.post (mapTransition t) (mapPlace p) = N₁.post t p)
    (hPreZero :
      ∀ (t : N₁.Transition) (q : N₂.Place),
        (¬ ∃ p : N₁.Place, mapPlace p = q) →
          N₂.pre (mapTransition t) q = 0)
    (hPostZero :
      ∀ (t : N₁.Transition) (q : N₂.Place),
        (¬ ∃ p : N₁.Place, mapPlace p = q) →
          N₂.post (mapTransition t) q = 0)
    (M : N₁.Marking) (t : N₁.Transition) :
    mapMarking mapPlace (Petri.fire N₁ M t) =
      Petri.fire N₂ (mapMarking mapPlace M) (mapTransition t) := by
  apply Petri.Marking.ext
  intro q
  by_cases hMapped : ∃ p : N₁.Place, mapPlace p = q
  · obtain ⟨p, rfl⟩ := hMapped
    simp [Petri.fire_apply, hPre, hPost,
      mapMarking_apply hPlaceInj]
  · simp [Petri.fire_apply, hPreZero t q hMapped,
      hPostZero t q hMapped,
      mapMarking_zero_of_not_mapped M q hMapped,
      mapMarking_zero_of_not_mapped (Petri.fire N₁ M t) q hMapped]

theorem firingSequence_map
    {N₁ N₂ : Petri.Net}
    {mapPlace : N₁.Place → N₂.Place}
    {mapTransition : N₁.Transition → N₂.Transition}
    (hPlaceInj : Function.Injective mapPlace)
    (hPre :
      ∀ (t : N₁.Transition) (p : N₁.Place),
        N₂.pre (mapTransition t) (mapPlace p) = N₁.pre t p)
    (hPost :
      ∀ (t : N₁.Transition) (p : N₁.Place),
        N₂.post (mapTransition t) (mapPlace p) = N₁.post t p)
    (hPreZero :
      ∀ (t : N₁.Transition) (q : N₂.Place),
        (¬ ∃ p : N₁.Place, mapPlace p = q) →
          N₂.pre (mapTransition t) q = 0)
    (hPostZero :
      ∀ (t : N₁.Transition) (q : N₂.Place),
        (¬ ∃ p : N₁.Place, mapPlace p = q) →
          N₂.post (mapTransition t) q = 0)
    {M M' : N₁.Marking} {ts : List N₁.Transition}
    (hSeq : Petri.FiringSequence N₁ M ts M') :
    Petri.FiringSequence N₂
      (mapMarking mapPlace M) (ts.map mapTransition)
      (mapMarking mapPlace M') :=
  Petri.FiringSequence.map
    (mapMarking mapPlace) mapTransition
    (enabled_map hPlaceInj hPre hPreZero)
    (fire_map hPlaceInj hPre hPost hPreZero hPostZero)
    hSeq

end NetEmbedding

theorem loopBodyRoot_map_initial
    (body redo : POWL2 Activity) :
    NetEmbedding.mapMarking (loopBodyRootPlaceOf body redo)
        (target body).wfnet.initial =
      Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childEntry [] 0)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_body_entry_mem
                (Structural.normalize body) (Structural.normalize redo) [])) := by
  rw [Petri.WFNet.initial]
  rw [NetEmbedding.mapMarking_singleton
    (loopBodyRootPlaceOf_injective body redo)]
  rw [loopBodyRootPlace_initial]

theorem loopBodyRoot_map_final
    (body redo : POWL2 Activity) :
    NetEmbedding.mapMarking (loopBodyRootPlaceOf body redo)
        (target body).wfnet.final =
      Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childExit [] 0)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_body_exit_mem
                (Structural.normalize body) (Structural.normalize redo) [])) := by
  rw [Petri.WFNet.final]
  rw [NetEmbedding.mapMarking_singleton
    (loopBodyRootPlaceOf_injective body redo)]
  rw [loopBodyRootPlace_final]

theorem loopBodyRoot_firingSequence_map
    (body redo : POWL2 Activity)
    {M M' : (target body).wfnet.net.Marking}
    {ts : List (target body).wfnet.net.Transition}
    (hSeq : Petri.FiringSequence (target body).wfnet.net M ts M') :
    Petri.FiringSequence (target (POWL2.loop body redo)).wfnet.net
      (NetEmbedding.mapMarking (loopBodyRootPlaceOf body redo) M)
      (ts.map (loopBodyRootTransitionOf body redo))
      (NetEmbedding.mapMarking (loopBodyRootPlaceOf body redo) M') :=
  NetEmbedding.firingSequence_map
    (loopBodyRootPlaceOf_injective body redo)
    (loopBodyRootTransition_pre body redo)
    (loopBodyRootTransition_post body redo)
    (loopBodyRootTransition_pre_zero_of_not_mapped body redo)
    (loopBodyRootTransition_post_zero_of_not_mapped body redo)
    hSeq

theorem loopBodyRoot_firingSequence
    (body redo : POWL2 Activity)
    {ts : List (target body).wfnet.net.Transition}
    (hSeq : Petri.FiringSequence (target body).wfnet.net
      (target body).wfnet.initial ts (target body).wfnet.final) :
    Petri.FiringSequence (target (POWL2.loop body redo)).wfnet.net
      (Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childEntry [] 0)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_body_entry_mem
                (Structural.normalize body) (Structural.normalize redo) [])))
      (ts.map (loopBodyRootTransitionOf body redo))
      (Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childExit [] 0)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_body_exit_mem
                (Structural.normalize body) (Structural.normalize redo) []))) := by
  simpa [loopBodyRoot_map_initial body redo,
    loopBodyRoot_map_final body redo] using
    loopBodyRoot_firingSequence_map body redo hSeq

theorem loopRedoRoot_map_initial
    (body redo : POWL2 Activity) :
    NetEmbedding.mapMarking (loopRedoRootPlaceOf body redo)
        (target redo).wfnet.initial =
      Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childEntry [] 1)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_redo_entry_mem
                (Structural.normalize body) (Structural.normalize redo) [])) := by
  rw [Petri.WFNet.initial]
  rw [NetEmbedding.mapMarking_singleton
    (loopRedoRootPlaceOf_injective body redo)]
  rw [loopRedoRootPlace_initial]

theorem loopRedoRoot_map_final
    (body redo : POWL2 Activity) :
    NetEmbedding.mapMarking (loopRedoRootPlaceOf body redo)
        (target redo).wfnet.final =
      Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childExit [] 1)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_redo_exit_mem
                (Structural.normalize body) (Structural.normalize redo) [])) := by
  rw [Petri.WFNet.final]
  rw [NetEmbedding.mapMarking_singleton
    (loopRedoRootPlaceOf_injective body redo)]
  rw [loopRedoRootPlace_final]

theorem loopRedoRoot_firingSequence_map
    (body redo : POWL2 Activity)
    {M M' : (target redo).wfnet.net.Marking}
    {ts : List (target redo).wfnet.net.Transition}
    (hSeq : Petri.FiringSequence (target redo).wfnet.net M ts M') :
    Petri.FiringSequence (target (POWL2.loop body redo)).wfnet.net
      (NetEmbedding.mapMarking (loopRedoRootPlaceOf body redo) M)
      (ts.map (loopRedoRootTransitionOf body redo))
      (NetEmbedding.mapMarking (loopRedoRootPlaceOf body redo) M') :=
  NetEmbedding.firingSequence_map
    (loopRedoRootPlaceOf_injective body redo)
    (loopRedoRootTransition_pre body redo)
    (loopRedoRootTransition_post body redo)
    (loopRedoRootTransition_pre_zero_of_not_mapped body redo)
    (loopRedoRootTransition_post_zero_of_not_mapped body redo)
    hSeq

theorem loopRedoRoot_firingSequence
    (body redo : POWL2 Activity)
    {ts : List (target redo).wfnet.net.Transition}
    (hSeq : Petri.FiringSequence (target redo).wfnet.net
      (target redo).wfnet.initial ts (target redo).wfnet.final) :
    Petri.FiringSequence (target (POWL2.loop body redo)).wfnet.net
      (Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childEntry [] 1)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_redo_entry_mem
                (Structural.normalize body) (Structural.normalize redo) [])))
      (ts.map (loopRedoRootTransitionOf body redo))
      (Petri.Marking.singleton
        (placeOf (POWL2.loop body redo) (Structural.childExit [] 1)
          (by
            simpa [Structural.rawPlacesRoot, Structural.compiled,
              Structural.normalize] using
              Structural.loop_redo_exit_mem
                (Structural.normalize body) (Structural.normalize redo) []))) := by
  simpa [loopRedoRoot_map_initial body redo,
    loopRedoRoot_map_final body redo] using
    loopRedoRoot_firingSequence_map body redo hSeq

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
