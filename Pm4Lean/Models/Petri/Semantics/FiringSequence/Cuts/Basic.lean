import Pm4Lean.Models.Petri.Semantics.FiringSequence

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/--
A comparable pair of cuts inside one concrete run `ts` from `M₀` to `Mend`.
The run factors as `(pref ++ loop) ++ suffix`; the first cut reaches `M`, the
loop reaches `M'`, and the two cut markings form a strict cover.
-/
def ComparableCutTraceInRun
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking) :
    Prop :=
  ∃ pref loop suffix : List N.Transition,
    ∃ M M' : N.Marking,
      ts = (pref ++ loop) ++ suffix ∧
        FiringSequence N M₀ ts Mend ∧
          FiringSequence N M₀ pref M ∧
            FiringSequence N M loop M' ∧
              M ≤ M' ∧ M ≠ M'

/--
Forgetting the explicit ambient sequence of an in-run cut trace gives a local
factored run witness.
-/
theorem comparableCutTraceInRun_exists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (hTrace : ComparableCutTraceInRun N M₀ ts Mend) :
    ∃ pref loop suffix : List N.Transition,
      ∃ M M' : N.Marking,
        FiringSequence N M₀ ((pref ++ loop) ++ suffix) Mend ∧
          FiringSequence N M₀ pref M ∧
            FiringSequence N M loop M' ∧
              M ≤ M' ∧ M ≠ M' := by
  obtain ⟨pref, loop, suffix, M, M',
    hEq, hRun, hPref, hLoop, hLe, hNe⟩ := hTrace
  exact ⟨pref, loop, suffix, M, M',
    by simpa [hEq] using hRun,
    hPref,
    hLoop,
    hLe,
    hNe⟩

end FiringSequence
end Petri
end Pm4Lean
