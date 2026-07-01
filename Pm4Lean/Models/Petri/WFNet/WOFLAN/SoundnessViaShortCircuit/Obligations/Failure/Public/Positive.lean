import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Obligations.Failure.Public.Negative

namespace Pm4Lean
namespace Petri

theorem woflanProofObligations_of_original_bounded
    {W : WFNet}
    (hBounded : TokenBoundedReachableOriginal W) :
    WoflanProofObligations W :=
  Classical.byContradiction (fun hNotObligations =>
    not_original_bounded_of_not_woflanProofObligations
      hNotObligations hBounded)

theorem woflanProofObligations_of_shortCircuit_bounded
    {W : WFNet}
    (hBounded : Bounded (shortCircuit W) W.initial) :
    WoflanProofObligations W :=
  woflanProofObligations_of_original_bounded
    (original_bounded_of_shortCircuit_bounded hBounded)

theorem woflanProofObligations_of_live_and_bounded_shortCircuit
    {W : WFNet}
    (hLiveBounded :
      Live (shortCircuit W) W.initial ∧
        Bounded (shortCircuit W) W.initial) :
    WoflanProofObligations W :=
  woflanProofObligations_of_shortCircuit_bounded hLiveBounded.2

end Petri
end Pm4Lean
