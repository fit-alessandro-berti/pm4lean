import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_subset
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates coordinates' : List (List Nat)}
    (hSubset : ∀ coords : List Nat, coords ∈ coordinates → coords ∈ coordinates')
    (hCovered :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
        samples coordinates) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
      samples coordinates' := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨coords, hMem, hLe⟩ :=
    hCovered sample hSampleMem hNoPredecessor
  exact ⟨coords, hSubset coords hMem, hLe⟩

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_cons
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (coords : List Nat) {coordinates : List (List Nat)}
    (hCovered :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
        samples coordinates) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
      samples (coords :: coordinates) :=
  noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => by simp [hMem])
    hCovered

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_append_left
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates extra : List (List Nat)}
    (hCovered :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
        samples coordinates) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
      samples (coordinates ++ extra) :=
  noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => List.mem_append_left extra hMem)
    hCovered

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_append_right
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates extra : List (List Nat)}
    (hCovered :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
        samples extra) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy
      samples (coordinates ++ extra) :=
  noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_subset
    (fun _ hMem => List.mem_append_right coordinates hMem)
    hCovered

end FiringSequence
end Petri
end Pm4Lean
