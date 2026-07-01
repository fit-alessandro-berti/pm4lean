import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_markingsDominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking}
    (hDominated :
      NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (markings.map (fun M => Marking.placeValues N M)) := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨M, hMem, hLe⟩ :=
    hDominated sample hSampleMem hNoPredecessor
  exact ⟨Marking.placeValues N M, by
    simp
    exact ⟨M, hMem, rfl⟩,
    Marking.placeValues_le_of_le hLe⟩

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_of_coordinateLists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {markings : List N.Marking}
    (hCoordinates :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
        (markings.map (fun M => Marking.placeValues N M))) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples markings := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨coords, hCoordsMem, hLeCoords⟩ :=
    hCoordinates sample hSampleMem hNoPredecessor
  rw [List.mem_map] at hCoordsMem
  obtain ⟨M, hMem, hEq⟩ := hCoordsMem
  exact ⟨M, hMem, by
    apply Marking.le_of_placeValues_le
    rw [hEq]
    exact hLeCoords⟩

theorem noComparablePrefixCutPredecessorMarkingsDominatedBy_of_coordinateCover
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)}
    (hCoordinates :
      NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
        coordinates) :
    NoComparablePrefixCutPredecessorMarkingsDominatedBy samples
      (coordinates.map (fun coords => Marking.ofValuesOn N.places coords)) := by
  intro sample hSampleMem hNoPredecessor
  obtain ⟨coords, hCoordsMem, hLeCoords⟩ :=
    hCoordinates sample hSampleMem hNoPredecessor
  exact ⟨Marking.ofValuesOn N.places coords, by
    simp
    exact ⟨coords, hCoordsMem, rfl⟩,
    Marking.le_of_placeValues_le_coords N hLeCoords⟩

end FiringSequence
end Petri
end Pm4Lean
