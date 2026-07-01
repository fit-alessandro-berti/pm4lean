import Pm4Lean.Models.Petri.Behavior.Boundedness.Samples
import Pm4Lean.Models.Petri.Basic.Marking.Coordinates.Box
import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Bounded

namespace Pm4Lean
namespace Petri

namespace FiringSequence

def NoComparablePrefixCutPredecessorMarkingsCovered
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend))
    (markings : List N.Marking) : Prop :=
  ∀ sample : PrefixCutSample N M₀ ts Mend,
    sample ∈ samples →
      ¬ HasComparablePrefixCutPredecessor sample →
        ∃ M : N.Marking, M ∈ markings ∧ sample.marking = M

def NoComparablePrefixCutPredecessorMarkingsDominatedBy
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend))
    (markings : List N.Marking) : Prop :=
  ∀ sample : PrefixCutSample N M₀ ts Mend,
    sample ∈ samples →
      ¬ HasComparablePrefixCutPredecessor sample →
        ∃ M : N.Marking, M ∈ markings ∧ sample.marking ≤ M

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_of_covered
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsCovered samples markings) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨M, hMem, hEq⟩ :=
    hCovered sample hSampleMem hNoPredecessor
  exact ⟨M, hMem, by
    intro p
    rw [hEq]
    exact Nat.le_refl _⟩

theorem noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking} {k : Nat}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings)
    (hBounded :
      ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    NoComparablePrefixCutPredecessorsBounded samples k := by
  intro sample hSampleMem hNoPredecessor p
  obtain ⟨M, hMem, hLe⟩ :=
    hCovered sample hSampleMem hNoPredecessor
  exact Nat.le_trans (hLe p) (hBounded M hMem p)

theorem noComparablePrefixCutPredecessorsBounded_of_markingsCoveredExact
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking} {k : Nat}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsCovered samples markings)
    (hBounded :
      ∀ M : N.Marking, M ∈ markings → ∀ p : N.Place, M p ≤ k) :
    NoComparablePrefixCutPredecessorsBounded samples k :=
  noComparablePrefixCutPredecessorsBounded_of_markingsCovered
    (noComparablePrefixCutPredecessorMarkingsDominatedBy_of_covered hCovered)
    hBounded

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_boundedBox
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)} {k : Nat}
    (hBounded : NoComparablePrefixCutPredecessorsBounded samples k) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy
      samples (Marking.boundedPlaceValueMarkings N k) := by
  intro sample hSampleMem hNoPredecessor
  exact Marking.exists_mem_boundedPlaceValueMarkings_ge_of_forall_le
    (hBounded sample hSampleMem hNoPredecessor)

theorem noComparablePrefixCutPredecessorsBounded_of_samplesBounded
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings)
    (hBounded : SamplesBounded N markings) :
    ∃ k : Nat, NoComparablePrefixCutPredecessorsBounded samples k := by
  obtain ⟨k, hBoundedAtK⟩ := hBounded
  exact ⟨k,
    noComparablePrefixCutPredecessorsBounded_of_markingsCovered
      hCovered hBoundedAtK⟩

end FiringSequence
end Petri
end Pm4Lean
