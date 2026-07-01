import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.NoPredecessor.Basic
import Pm4Lean.Util.NatListBasis.Transfer

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_noPredecessorSampleCoordinates
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (prefixCutNoPredecessorSampleCoordinateLists samples) := by
  intro sample hSampleMem hNoPredecessor
  exact ⟨Marking.placeValues N sample.marking,
    mem_prefixCutNoPredecessorSampleCoordinateLists_of_mem
      hSampleMem hNoPredecessor,
    natListLe_refl (Marking.placeValues N sample.marking)⟩

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_noPredecessorGreedy
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (natListGreedyBasis
        (prefixCutNoPredecessorSampleCoordinateLists samples)) := by
  rw [noComparablePrefixCutPredecessorCoordinateListsDominatedBy_iff_dominatedBy]
  intro sample hSampleMem hNoPredecessor
  exact natListGreedyBasis_dominatesAll
    (prefixCutNoPredecessorSampleCoordinateLists samples)
    (Marking.placeValues N sample.marking)
    (mem_prefixCutNoPredecessorSampleCoordinateLists_of_mem
      hSampleMem hNoPredecessor)

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_noPredecessorGreedy_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)}
    (hGreedyDominated :
      NatListBasisDominatesAll
        (natListGreedyBasis
          (prefixCutNoPredecessorSampleCoordinateLists samples))
        coordinates) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      coordinates := by
  rw [noComparablePrefixCutPredecessorCoordinateListsDominatedBy_iff_dominatedBy]
  intro sample hSampleMem hNoPredecessor
  exact natListBasisDominatesAll_of_greedy_dominated hGreedyDominated
    (Marking.placeValues N sample.marking)
    (mem_prefixCutNoPredecessorSampleCoordinateLists_of_mem
      hSampleMem hNoPredecessor)

end FiringSequence
end Petri
end Pm4Lean
