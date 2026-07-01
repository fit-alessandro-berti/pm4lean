import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/-- A single prefix cut of a concrete run. -/
def PrefixCutInRun
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking)
    (pref : List N.Transition) (M : N.Marking) : Prop :=
  ∃ suffix : List N.Transition,
    ts = pref ++ suffix ∧
      FiringSequence N M₀ ts Mend ∧
        FiringSequence N M₀ pref M

/--
Two prefix cuts of the same run where the second prefix extends the first and
the reached markings are comparable and distinct.
-/
def ComparablePrefixCutPairInRun
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking) :
    Prop :=
  ∃ pref prefLoop loop : List N.Transition,
    ∃ M M' : N.Marking,
      prefLoop = pref ++ loop ∧
        PrefixCutInRun N M₀ ts Mend pref M ∧
          PrefixCutInRun N M₀ ts Mend prefLoop M' ∧
            M ≤ M' ∧ M ≠ M'

/--
The form produced directly by a cut enumeration: both cut markings are reached
as prefixes of the same run, at `pref` and at `pref ++ loop`.
-/
def PrefixComparableCutTraceInRun
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking) :
    Prop :=
  ∃ pref loop suffix : List N.Transition,
    ∃ M M' : N.Marking,
      ts = (pref ++ loop) ++ suffix ∧
        FiringSequence N M₀ ts Mend ∧
          FiringSequence N M₀ pref M ∧
            FiringSequence N M₀ (pref ++ loop) M' ∧
              M ≤ M' ∧ M ≠ M'

theorem prefixComparableCutTraceInRun_of_pair
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hPair : ComparablePrefixCutPairInRun N M₀ ts Mend) :
    PrefixComparableCutTraceInRun N M₀ ts Mend := by
  obtain ⟨pref, prefLoop, loop, M, M',
    hPrefLoopEq, hPrefCut, hPrefLoopCut, hLe, hNe⟩ := hPair
  obtain ⟨_suffix₁, _hEq₁, _hRun₁, hPref⟩ := hPrefCut
  obtain ⟨suffix, hEq, hRun, hPrefLoop⟩ := hPrefLoopCut
  exact ⟨pref, loop, suffix, M, M',
    by simpa [hPrefLoopEq] using hEq,
    hRun,
    hPref,
    by simpa [hPrefLoopEq] using hPrefLoop,
    hLe,
    hNe⟩

theorem comparableCutTraceInRun_of_prefix
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hTrace : PrefixComparableCutTraceInRun N M₀ ts Mend) :
    ComparableCutTraceInRun N M₀ ts Mend := by
  obtain ⟨pref, loop, suffix, M, M',
    hEq, hRun, hPref, hPrefLoop, hLe, hNe⟩ := hTrace
  exact ⟨pref, loop, suffix, M, M',
    hEq,
    hRun,
    hPref,
    between_prefixes hPref hPrefLoop,
    hLe,
    hNe⟩

end FiringSequence
end Petri
end Pm4Lean
