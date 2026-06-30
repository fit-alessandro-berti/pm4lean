import Pm4Lean.Models.Petri.WFNet.WOFLAN.SoundnessViaShortCircuit.Iff
import Pm4Lean.Models.Petri.WFNet.WOFLAN.Boundedness.SelfCover

namespace Pm4Lean
namespace Petri

/--
The remaining proof obligations for the classic WOFLAN theorem

`Sound W ↔ Live (shortCircuit W) W.initial ∧ Bounded (shortCircuit W) W.initial`.

The only remaining field is the finite/Dickson extraction: there is a finite
threshold above which every concrete run contains a comparable cut trace.  The
token-sum lemmas already turn unbounded markings into arbitrarily long runs,
and the cut-trace and sequence lemmas then turn comparable cuts into the
prefix/loop self-cover excluded by soundness.
-/
structure WoflanProofObligations (W : WFNet) : Prop where
  long_run_comparable_cut_trace_threshold :
    HasLongRunComparableCutTraceThreshold W

theorem original_bounded_of_sound_and_woflan_obligations
    {W : WFNet}
    (hObligations : WoflanProofObligations W)
    (hSound : Sound W) :
    TokenBoundedReachableOriginal W :=
  original_bounded_of_sound_and_firingSequence_self_cover_extraction
    (unboundedOriginalProducesFiringSequenceSelfCover_of_largeSequences
      (largeSequencesProduceFiringSequenceSelfCover_of_cut
        (largeSequencesProduceCutSelfCover_of_factoredRun
          (largeSequencesProduceFactoredRunCutSelfCover_of_comparableCuts
            (largeSequencesProduceComparableCutsInRun_of_longRuns
              (longRunsProduceComparableCutsInRun_of_threshold_exists
                hObligations.long_run_comparable_cut_trace_threshold))))))
    hSound

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
        (original_bounded_of_sound_and_woflan_obligations
          hObligations hSound)).1 hSound
  · intro hLiveBounded
    exact live_and_bounded_shortCircuit_implies_sound
      hLiveBounded.1 hLiveBounded.2

end Petri
end Pm4Lean
