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

end TargetShape

end POWL2ToSoundWfNet
end ProcessModel
end Pm4Lean
