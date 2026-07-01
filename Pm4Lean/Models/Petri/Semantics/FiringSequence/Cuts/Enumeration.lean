import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Constructors
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def consPrefixCutSample
    {N : Net} {M₀ Mend : N.Marking} {t : N.Transition}
    {ts : List N.Transition}
    (hEnabled : Enabled N M₀ t)
    (hTail : FiringSequence N (fire N M₀ t) ts Mend)
    (sample : PrefixCutSample N (fire N M₀ t) ts Mend) :
    PrefixCutSample N M₀ (t :: ts) Mend where
  pref := t :: sample.pref
  marking := sample.marking
  isCut := by
    obtain ⟨suffix, hEq, _hTailRun, hPref⟩ := sample.isCut
    exact ⟨suffix,
      by simp [hEq],
      FiringSequence.cons hEnabled hTail,
      FiringSequence.cons hEnabled hPref⟩

theorem prefixCutSamples_cover_exists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hRun : FiringSequence N M₀ ts Mend) :
    ∃ samples : List (PrefixCutSample N M₀ ts Mend),
      PrefixCutsCoveredBySamples samples := by
  induction hRun with
  | nil M =>
      refine ⟨[initialPrefixCutSample (FiringSequence.nil M)], ?_⟩
      intro pref M' hCut
      obtain ⟨suffix, hEq, _hRun, hPref⟩ := hCut
      cases pref with
      | nil =>
          have hMarking : M = M' := deterministic (FiringSequence.nil M) hPref
          subst hMarking
          exact ⟨initialPrefixCutSample (FiringSequence.nil M),
            by simp,
            rfl,
            rfl⟩
      | cons t pref =>
          cases hEq
  | cons hEnabled hTail ih =>
      obtain ⟨tailSamples, hTailCovered⟩ := ih
      refine ⟨initialPrefixCutSample (FiringSequence.cons hEnabled hTail) ::
        tailSamples.map (consPrefixCutSample hEnabled hTail), ?_⟩
      intro pref M' hCut
      obtain ⟨suffix, hEq, _hRun, hPref⟩ := hCut
      cases pref with
      | nil =>
          have hMarking : _ = M' :=
            deterministic (FiringSequence.nil _) hPref
          subst hMarking
          exact ⟨initialPrefixCutSample (FiringSequence.cons hEnabled hTail),
            by simp,
            rfl,
            rfl⟩
      | cons t' prefTail =>
          cases hEq
          cases hPref with
          | cons hEnabled' hPrefTail =>
              have hTailCut :
                  PrefixCutInRun _ _ _ _ prefTail M' :=
                ⟨suffix, rfl, hTail, hPrefTail⟩
              obtain ⟨sample, hMem, hPrefEq, hMarkingEq⟩ :=
                hTailCovered prefTail M' hTailCut
              exact ⟨consPrefixCutSample hEnabled hTail sample,
                by
                  simp only [List.mem_cons, List.mem_map]
                  exact Or.inr ⟨sample, hMem, rfl⟩,
                by simp [consPrefixCutSample, hPrefEq],
                by simpa [consPrefixCutSample] using hMarkingEq⟩

end FiringSequence
end Petri
end Pm4Lean
