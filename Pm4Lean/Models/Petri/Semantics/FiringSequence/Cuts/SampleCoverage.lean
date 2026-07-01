import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Samples

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/-- A finite sample list contains every prefix cut of the run. -/
def PrefixCutsCoveredBySamples
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∀ pref : List N.Transition,
    ∀ M : N.Marking,
      PrefixCutInRun N M₀ ts Mend pref M →
        ∃ sample : PrefixCutSample N M₀ ts Mend,
                 sample ∈ samples ∧
                   sample.pref = pref ∧
                     sample.marking = M

theorem prefixCutsCoveredBySamples_of_subset
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples samples' : List (PrefixCutSample N M₀ ts Mend)}
    (hSubset : ∀ sample, sample ∈ samples → sample ∈ samples')
    (hCovered : PrefixCutsCoveredBySamples samples) :
    PrefixCutsCoveredBySamples samples' := by
  intro pref M hCut
  obtain ⟨sample, hMem, hPref, hMarking⟩ := hCovered pref M hCut
  exact ⟨sample, hSubset sample hMem, hPref, hMarking⟩

theorem prefixCutsCoveredBySamples_cons
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (sample : PrefixCutSample N M₀ ts Mend)
    (hCovered : PrefixCutsCoveredBySamples samples) :
    PrefixCutsCoveredBySamples (sample :: samples) :=
  prefixCutsCoveredBySamples_of_subset
    (fun _ hMem => by simp [hMem])
    hCovered

theorem containsComparablePrefixCutSamplePair_of_covered_pair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hCovered : PrefixCutsCoveredBySamples samples)
    (hPair : ComparablePrefixCutPairInRun N M₀ ts Mend) :
    ContainsComparablePrefixCutSamplePair samples := by
  obtain ⟨pref, prefLoop, loop, M, M',
    hPrefLoop, hPrefCut, hPrefLoopCut, hLe, hNe⟩ := hPair
  obtain ⟨first, hFirstMem, hFirstPref, hFirstMarking⟩ :=
    hCovered pref M hPrefCut
  obtain ⟨second, hSecondMem, hSecondPref, hSecondMarking⟩ :=
    hCovered prefLoop M' hPrefLoopCut
  exact ⟨first, second, hFirstMem, hSecondMem,
    ⟨loop,
      by
        calc
          second.pref = prefLoop := hSecondPref
          _ = pref ++ loop := hPrefLoop
          _ = first.pref ++ loop := by rw [hFirstPref]
      ,
      by
        intro p
        rw [hFirstMarking, hSecondMarking]
        exact hLe p,
      by
        intro hEq
        apply hNe
        ext p
        have hPoint := congrFun hEq p
        simpa [hFirstMarking, hSecondMarking] using hPoint⟩⟩

end FiringSequence
end Petri
end Pm4Lean
