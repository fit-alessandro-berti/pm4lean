import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def HasComparablePrefixCutPredecessor
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (second : PrefixCutSample N M₀ ts Mend) : Prop :=
  ∃ pref loop : List N.Transition,
    ∃ M : N.Marking,
      second.pref = pref ++ loop ∧
        PrefixCutInRun N M₀ ts Mend pref M ∧
          M ≤ second.marking ∧ M ≠ second.marking

def LargeSamplesHaveComparablePrefixCutPredecessor
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) (k : Nat) : Prop :=
  ∀ second : PrefixCutSample N M₀ ts Mend,
    second ∈ samples →
      (∃ p : N.Place, k < second.marking p) →
        HasComparablePrefixCutPredecessor second

theorem hasComparablePrefixPredecessor_of_cut
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {second : PrefixCutSample N M₀ ts Mend}
    (hCovered : PrefixCutsCoveredBySamples samples)
    (hCutPredecessor : HasComparablePrefixCutPredecessor second) :
    HasComparablePrefixPredecessor samples second := by
  obtain ⟨pref, loop, M, hSecondPref, hCut, hLe, hNe⟩ :=
    hCutPredecessor
  obtain ⟨first, hFirstMem, hFirstPref, hFirstMarking⟩ :=
    hCovered pref M hCut
  exact ⟨first, hFirstMem,
    ⟨loop,
      by
        calc
          second.pref = pref ++ loop := hSecondPref
          _ = first.pref ++ loop := by rw [hFirstPref]
      ,
      by
        intro p
        rw [hFirstMarking]
        exact hLe p,
      by
        intro hEq
        apply hNe
        ext p
        have hPoint := congrFun hEq p
        simpa [hFirstMarking] using hPoint⟩⟩

theorem largeSamplesHaveComparablePrefixPredecessor_of_cut
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hCovered : PrefixCutsCoveredBySamples samples)
    (hCutPredecessor :
      LargeSamplesHaveComparablePrefixCutPredecessor samples k) :
    LargeSamplesHaveComparablePrefixPredecessor samples k := by
  intro second hSecondMem hLarge
  exact hasComparablePrefixPredecessor_of_cut hCovered
    (hCutPredecessor second hSecondMem hLarge)

end FiringSequence
end Petri
end Pm4Lean
