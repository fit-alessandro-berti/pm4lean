import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.PrefixOrder

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def EqualPrefixCutCycleInRun
    (N : Net) (M₀ : N.Marking) (ts : List N.Transition) (Mend : N.Marking) :
    Prop :=
  ∃ pref loop suffix : List N.Transition,
    ∃ M : N.Marking,
      ts = (pref ++ loop) ++ suffix ∧
        FiringSequence N M₀ ts Mend ∧
          FiringSequence N M₀ pref M ∧
            FiringSequence N M loop M

theorem equalPrefixCutCycleInRun_of_samples_prefix_comparable_eq
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {first second : PrefixCutSample N M₀ ts Mend}
    (hEq : first.marking = second.marking)
    (hComparable :
      (∃ loop, second.pref = first.pref ++ loop) ∨
        ∃ loop, first.pref = second.pref ++ loop) :
    EqualPrefixCutCycleInRun N M₀ ts Mend := by
  cases hComparable with
  | inl hSecondExtends =>
      obtain ⟨loop, hSecondPref⟩ := hSecondExtends
      obtain ⟨suffix, hTs, hRun, hSecondRun⟩ := second.isCut
      obtain ⟨_firstSuffix, _hFirstTs, _hFirstRun, hFirstRun⟩ :=
        first.isCut
      have hLoop : FiringSequence N first.marking loop second.marking :=
        between_prefixes hFirstRun (by
          simpa [hSecondPref] using hSecondRun)
      exact ⟨first.pref, loop, suffix, first.marking,
        by simpa [hSecondPref] using hTs,
        hRun,
        hFirstRun,
        by simpa [hEq] using hLoop⟩
  | inr hFirstExtends =>
      obtain ⟨loop, hFirstPref⟩ := hFirstExtends
      obtain ⟨suffix, hTs, hRun, hFirstRun⟩ := first.isCut
      obtain ⟨_secondSuffix, _hSecondTs, _hSecondRun, hSecondRun⟩ :=
        second.isCut
      have hLoop : FiringSequence N second.marking loop first.marking :=
        between_prefixes hSecondRun (by
          simpa [hFirstPref] using hFirstRun)
      exact ⟨second.pref, loop, suffix, second.marking,
        by simpa [hFirstPref] using hTs,
        hRun,
        hSecondRun,
        by simpa [hEq] using hLoop⟩

end FiringSequence
end Petri
end Pm4Lean
