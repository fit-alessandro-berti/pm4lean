import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Length

namespace Pm4Lean
namespace Petri

namespace FiringSequence

/--
Prefix-cut sample coordinate vectors restricted to samples without a comparable
raw prefix-cut predecessor.
-/
noncomputable def prefixCutNoPredecessorSampleCoordinateLists
    {N : Net} {M₀ : N.Marking} {ts : List N.Transition} {Mend : N.Marking}
    (samples : List (PrefixCutSample N M₀ ts Mend)) : List (List Nat) := by
  classical
  exact
    (samples.filter
      (fun sample => ¬ HasComparablePrefixCutPredecessor sample)).map
        (fun sample => Marking.placeValues N sample.marking)

theorem mem_prefixCutNoPredecessorSampleCoordinateLists_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {sample : PrefixCutSample N M₀ ts Mend}
    (hMem : sample ∈ samples)
    (hNoPredecessor : ¬ HasComparablePrefixCutPredecessor sample) :
    Marking.placeValues N sample.marking ∈
      prefixCutNoPredecessorSampleCoordinateLists samples := by
  classical
  rw [prefixCutNoPredecessorSampleCoordinateLists, List.mem_map]
  exact ⟨sample, by simp [hMem, hNoPredecessor], rfl⟩

theorem exists_sample_of_mem_prefixCutNoPredecessorSampleCoordinateLists
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem : coords ∈ prefixCutNoPredecessorSampleCoordinateLists samples) :
    ∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧
        ¬ HasComparablePrefixCutPredecessor sample ∧
          coords = Marking.placeValues N sample.marking := by
  classical
  rw [prefixCutNoPredecessorSampleCoordinateLists, List.mem_map] at hMem
  obtain ⟨sample, hSampleMem, hEq⟩ := hMem
  have hFiltered :
      sample ∈ samples ∧ ¬ HasComparablePrefixCutPredecessor sample := by
    simpa using hSampleMem
  exact ⟨sample, hFiltered.1, hFiltered.2, hEq.symm⟩

theorem prefixCutNoPredecessorSampleCoordinateLists_length_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem : coords ∈ prefixCutNoPredecessorSampleCoordinateLists samples) :
    coords.length = N.places.length := by
  obtain ⟨sample, _hSampleMem, _hNoPredecessor, hCoordsEq⟩ :=
    exists_sample_of_mem_prefixCutNoPredecessorSampleCoordinateLists hMem
  rw [hCoordsEq, Marking.placeValues_length]

end FiringSequence
end Petri
end Pm4Lean
