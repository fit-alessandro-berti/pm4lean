import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Cover.Greedy.Membership

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem le_natListMax_coordinates_flatten_of_mem_greedyPrefixCutSampleCoordinateBasis
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coords : List Nat} {x : Nat}
    (hCoordsMem :
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists samples))
    (hXMem : x ∈ coords) :
    x ≤ NatListMax (prefixCutSampleCoordinateLists samples).flatten :=
  le_natListMax_flatten_of_mem_natListGreedyBasis hCoordsMem hXMem

theorem greedyPrefixCutSampleCoordinateBasis_boundedBy_localMax
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∀ coords : List Nat,
      coords ∈ natListGreedyBasis
        (prefixCutSampleCoordinateLists samples) →
        ∀ x : Nat, x ∈ coords →
          x ≤ NatListMax
            (prefixCutSampleCoordinateLists samples).flatten := by
  intro coords hCoordsMem x hXMem
  exact
    le_natListMax_coordinates_flatten_of_mem_greedyPrefixCutSampleCoordinateBasis
      hCoordsMem hXMem

theorem exists_greedyPrefixCutSampleCoordinateBasis_bound
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    ∃ k : Nat,
      ∀ coords : List Nat,
        coords ∈ natListGreedyBasis
          (prefixCutSampleCoordinateLists samples) →
          ∀ x : Nat, x ∈ coords → x ≤ k :=
  ⟨NatListMax (prefixCutSampleCoordinateLists samples).flatten,
    greedyPrefixCutSampleCoordinateBasis_boundedBy_localMax samples⟩

end FiringSequence
end Petri
end Pm4Lean
