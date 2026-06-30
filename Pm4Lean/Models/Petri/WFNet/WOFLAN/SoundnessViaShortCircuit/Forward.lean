import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness

namespace Pm4Lean
namespace Petri

theorem sound_implies_live_and_bounded_shortCircuit_of_original_bounded
    {W : WFNet}
    (hSound : Sound W)
    (hBoundOriginal : TokenBoundedReachableOriginal W) :
    Live (shortCircuit W) W.initial ∧
      Bounded (shortCircuit W) W.initial :=
  ⟨live_of_sound hSound,
    shortCircuit_bounded_of_original_bounded_and_sound
      hBoundOriginal hSound⟩

end Petri
end Pm4Lean
