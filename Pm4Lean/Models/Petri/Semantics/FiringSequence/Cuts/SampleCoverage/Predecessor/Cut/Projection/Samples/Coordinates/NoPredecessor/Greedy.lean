import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.NoPredecessor.Cover

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem greedyPrefixCutNoPredecessorSampleCoordinateBasis_length_of_mem
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat}
    (hMem :
      coords ∈ natListGreedyBasis
        (prefixCutNoPredecessorSampleCoordinateLists samples)) :
    coords.length = N.places.length :=
  prefixCutNoPredecessorSampleCoordinateLists_length_of_mem
    (mem_natListGreedyBasis hMem)

theorem exists_sample_place_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat} {x : Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutNoPredecessorSampleCoordinateLists samples))
    (hXMem : x ∈ coords) :
    ∃ sample : PrefixCutSample N M₀ ts Mend,
      sample ∈ samples ∧
        ¬ HasComparablePrefixCutPredecessor sample ∧
          ∃ p : N.Place, x = sample.marking p := by
  obtain ⟨sample, hSampleMem, hNoPredecessor, hCoordsEq⟩ :=
    exists_sample_of_mem_prefixCutNoPredecessorSampleCoordinateLists
      (mem_natListGreedyBasis hCoordsMem)
  obtain ⟨p, hValueEq⟩ :=
    Marking.exists_place_of_mem_placeValues
      N (M := sample.marking) (by simpa [hCoordsEq] using hXMem)
  exact ⟨sample, hSampleMem, hNoPredecessor, p, hValueEq⟩

theorem le_natListMax_filteredCoordinates_flatten_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat} {x : Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutNoPredecessorSampleCoordinateLists samples))
    (hXMem : x ∈ coords) :
    x ≤ NatListMax
      (prefixCutNoPredecessorSampleCoordinateLists samples).flatten :=
  le_natListMax_flatten_of_mem_natListGreedyBasis hCoordsMem hXMem

theorem greedyPrefixCutNoPredecessorSampleCoordinateBasis_boundedBy_localMax
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∀ coords : List Nat,
      coords ∈ natListGreedyBasis
        (prefixCutNoPredecessorSampleCoordinateLists samples) →
        ∀ x : Nat, x ∈ coords →
          x ≤ NatListMax
            (prefixCutNoPredecessorSampleCoordinateLists samples).flatten := by
  intro coords hCoordsMem x hXMem
  exact
    le_natListMax_filteredCoordinates_flatten_of_mem_greedyPrefixCutNoPredecessorSampleCoordinateBasis
      hCoordsMem hXMem

theorem exists_greedyPrefixCutNoPredecessorSampleCoordinateBasis_bound
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∃ k : Nat,
      ∀ coords : List Nat,
        coords ∈ natListGreedyBasis
          (prefixCutNoPredecessorSampleCoordinateLists samples) →
          ∀ x : Nat, x ∈ coords → x ≤ k :=
  ⟨NatListMax
      (prefixCutNoPredecessorSampleCoordinateLists samples).flatten,
    greedyPrefixCutNoPredecessorSampleCoordinateBasis_boundedBy_localMax
      samples⟩

end FiringSequence
end Petri
end Pm4Lean
