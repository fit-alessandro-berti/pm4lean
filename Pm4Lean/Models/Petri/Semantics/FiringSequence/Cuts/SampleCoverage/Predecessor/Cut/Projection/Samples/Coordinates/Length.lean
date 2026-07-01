import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem prefixCutSampleCoordinateLists_length_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem : coords ∈ prefixCutSampleCoordinateLists samples) :
    coords.length = N.places.length := by
  obtain ⟨sample, _hSampleMem, hEq⟩ :=
    exists_sample_of_mem_prefixCutSampleCoordinateLists hMem
  rw [hEq, Marking.placeValues_length]

theorem sample_placeValues_length
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (sample : PrefixCutSample N M₀ ts Mend) :
    (Marking.placeValues N sample.marking).length = N.places.length :=
  Marking.placeValues_length N sample.marking

theorem basisGreaterCoordinateWitness_sampleCoordinates_of_not_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    (sample : PrefixCutSample N M₀ ts Mend)
    (hNotDominated :
      ¬ NatListDominatedBy
        (Marking.placeValues N sample.marking)
        (prefixCutSampleCoordinateLists samples)) :
    NatListBasisHasGreaterCoordinateWitness
      (Marking.placeValues N sample.marking)
      (prefixCutSampleCoordinateLists samples) :=
  natListBasisHasGreaterCoordinateWitness_of_not_dominated_length_eq
    (sample_placeValues_length sample)
    (fun _ hMem => prefixCutSampleCoordinateLists_length_of_mem hMem)
    hNotDominated

end FiringSequence
end Petri
end Pm4Lean
