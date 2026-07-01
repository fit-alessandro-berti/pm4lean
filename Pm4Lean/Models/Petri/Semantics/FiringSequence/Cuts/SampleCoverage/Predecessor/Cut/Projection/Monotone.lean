import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_of_subset
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings markings' : List N.Marking}
    (hSubset : ∀ M : N.Marking, M ∈ markings → M ∈ markings')
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings' := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨M, hMem, hLe⟩ :=
    hCovered sample hSampleMem hNoPredecessor
  exact ⟨M, hSubset M hMem, hLe⟩

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_cons
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (M : N.Marking) {markings : List N.Marking}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples
      (M :: markings) :=
  noComparablePrefixCutPredecessorMarkingsDominatedBy_of_subset
    (fun _ hMem => by simp [hMem])
    hCovered

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_append_left
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings extra : List N.Marking}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples
      (markings ++ extra) :=
  noComparablePrefixCutPredecessorMarkingsDominatedBy_of_subset
    (fun _ hMem => by exact List.mem_append_left extra hMem)
    hCovered

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_append_right
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings extra : List N.Marking}
    (hCovered :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples extra) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples
      (markings ++ extra) :=
  noComparablePrefixCutPredecessorMarkingsDominatedBy_of_subset
    (fun _ hMem => by exact List.mem_append_right markings hMem)
    hCovered

end FiringSequence
end Petri
end Pm4Lean
