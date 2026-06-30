import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Iff

namespace Pm4Lean
namespace Petri

/--
The remaining proof obligations for the classic WOFLAN theorem

`Sound W ↔ Live (shortCircuit W) W.initial ∧ Bounded (shortCircuit W) W.initial`.

The only remaining field is the forward boundedness gap.  The reverse
proper-completion direction is discharged by the closed-form short-circuit
pumping proof in `Boundedness.Growth`.
-/
structure WoflanProofObligations (W : WFNet) : Prop where
  sound_bounds_original :
    Sound W → TokenBoundedReachableOriginal W

theorem sound_iff_live_and_bounded_shortCircuit_of_woflan_obligations
    {W : WFNet}
    (hObligations : WoflanProofObligations W) :
    Sound W ↔
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial := by
  constructor
  · intro hSound
    exact
      (sound_iff_live_and_bounded_shortCircuit_of_original_bounded
        (hObligations.sound_bounds_original hSound)).1 hSound
  · intro hLiveBounded
    exact live_and_bounded_shortCircuit_implies_sound
      hLiveBounded.1 hLiveBounded.2

end Petri
end Pm4Lean
