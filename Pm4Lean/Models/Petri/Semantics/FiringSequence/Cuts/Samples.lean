import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Prefix

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/-- A sampled prefix cut of a concrete run. -/
structure PrefixCutSample
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking)
    where
  pref : List N.Transition
  marking : N.Marking
  isCut : PrefixCutInRun N M₀ ts Mend pref marking

/--
Two sampled prefix cuts where the second sample extends the first and their
markings form a strict cover.
-/
def ComparablePrefixCutSamplePair
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (first second : PrefixCutSample N M₀ ts Mend) : Prop :=
  ∃ loop : List N.Transition,
    second.pref = first.pref ++ loop ∧
      first.marking ≤ second.marking ∧
        first.marking ≠ second.marking

def ContainsComparablePrefixCutSamplePair
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : Prop :=
  ∃ first second : PrefixCutSample N M₀ ts Mend,
    first ∈ samples ∧
    second ∈ samples ∧
        ComparablePrefixCutSamplePair first second

theorem comparablePrefixCutSamplePair_of_contains
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hContains : ContainsComparablePrefixCutSamplePair samples) :
    ∃ first second : PrefixCutSample N M₀ ts Mend,
      ComparablePrefixCutSamplePair first second := by
  obtain ⟨first, second, _hFirstMem, _hSecondMem, hPair⟩ := hContains
  exact ⟨first, second, hPair⟩

theorem comparablePrefixCutPairInRun_of_samples
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hPair : ComparablePrefixCutSamplePair first second) :
    ComparablePrefixCutPairInRun N M₀ ts Mend := by
  obtain ⟨loop, hPrefix, hLe, hNe⟩ := hPair
  exact ⟨first.pref, second.pref, loop, first.marking, second.marking,
    hPrefix,
    first.isCut,
    second.isCut,
    hLe,
    hNe⟩

theorem comparablePrefixCutPairInRun_of_sampleList
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (hContains : ContainsComparablePrefixCutSamplePair samples) :
    ComparablePrefixCutPairInRun N M₀ ts Mend := by
  obtain ⟨first, second, hPair⟩ :=
    comparablePrefixCutSamplePair_of_contains hContains
  exact comparablePrefixCutPairInRun_of_samples hPair

end FiringSequence
end Petri
end Pm4Lean
