import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.Samples

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem append_prefixes_comparable
    {α : Type u} {a b sa sb : List α}
    (h : a ++ sa = b ++ sb) :
    (∃ loop, b = a ++ loop) ∨ (∃ loop, a = b ++ loop) := by
  induction a generalizing b with
  | nil =>
      left
      exact ⟨b, by simp⟩
  | cons x as ih =>
      cases b with
      | nil =>
          right
          exact ⟨x :: as, by simp⟩
      | cons y bs =>
          simp only [List.cons_append] at h
          injection h with hHead hTail
          subst y
          obtain hLeft | hRight := ih (b := bs) hTail
          · obtain ⟨loop, hLoop⟩ := hLeft
            left
            exact ⟨loop, by simp [hLoop]⟩
          · obtain ⟨loop, hLoop⟩ := hRight
            right
            exact ⟨loop, by simp [hLoop]⟩

theorem prefixCutSamples_prefix_comparable
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (first second : PrefixCutSample N M₀ ts Mend) :
    (∃ loop, second.pref = first.pref ++ loop) ∨
      (∃ loop, first.pref = second.pref ++ loop) := by
  obtain ⟨suffixFirst, hFirstEq, _hRunFirst, _hPrefFirst⟩ := first.isCut
  obtain ⟨suffixSecond, hSecondEq, _hRunSecond, _hPrefSecond⟩ := second.isCut
  apply append_prefixes_comparable
  rw [← hFirstEq, ← hSecondEq]

end FiringSequence
end Petri
end Pm4Lean
