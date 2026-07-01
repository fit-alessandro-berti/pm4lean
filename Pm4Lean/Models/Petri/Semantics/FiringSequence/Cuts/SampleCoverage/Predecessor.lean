import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Large

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def HasComparablePrefixPredecessor
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend))
    (second : PrefixCutSample N M₀ ts Mend) : Prop :=
  ∃ first : PrefixCutSample N M₀ ts Mend,
    first ∈ samples ∧ ComparablePrefixCutSamplePair first second

def LargeSamplesHaveComparablePrefixPredecessor
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) (k : Nat) : Prop :=
  ∀ second : PrefixCutSample N M₀ ts Mend,
    second ∈ samples →
      (∃ p : N.Place, k < second.marking p) →
        HasComparablePrefixPredecessor samples second

theorem containsComparablePrefixCutSamplePair_of_large_predecessor
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hLarge : ContainsLargePrefixCutSample samples k)
    (hPredecessor : LargeSamplesHaveComparablePrefixPredecessor samples k) :
    ContainsComparablePrefixCutSamplePair samples := by
  obtain ⟨second, hSecondMem, hSecondLarge⟩ := hLarge
  obtain ⟨first, hFirstMem, hPair⟩ :=
    hPredecessor second hSecondMem hSecondLarge
  exact ⟨first, second, hFirstMem, hSecondMem, hPair⟩

end FiringSequence
end Petri
end Pm4Lean
