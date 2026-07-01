import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def ContainsLargePrefixCutSample
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) (k : Nat) : Prop :=
  ∃ sample : PrefixCutSample N M₀ ts Mend,
    sample ∈ samples ∧
      ∃ p : N.Place, k < sample.marking p

theorem prefixCutsCoveredBySamples_full
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hRun : FiringSequence N M₀ ts Mend)
    (hCovered : PrefixCutsCoveredBySamples samples) :
    ∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧ sample.pref = ts ∧ sample.marking = Mend :=
  hCovered ts Mend ⟨[], by simp, hRun, hRun⟩

theorem containsLargePrefixCutSample_of_final
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hRun : FiringSequence N M₀ ts Mend)
    (hCovered : PrefixCutsCoveredBySamples samples)
    (hLarge : ∃ p : N.Place, k < Mend p) :
    ContainsLargePrefixCutSample samples k := by
  obtain ⟨sample, hMem, _hPref, hMarking⟩ :=
    prefixCutsCoveredBySamples_full hRun hCovered
  obtain ⟨p, hLt⟩ := hLarge
  exact ⟨sample, hMem, p, by simpa [hMarking] using hLt⟩

end FiringSequence
end Petri
end Pm4Lean
