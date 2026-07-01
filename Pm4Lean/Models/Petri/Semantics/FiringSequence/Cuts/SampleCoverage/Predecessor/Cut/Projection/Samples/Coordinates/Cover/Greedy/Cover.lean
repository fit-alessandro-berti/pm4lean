import Pm4Lean.Models.Petri.Semantics.FiringSequence.Cuts.SampleCoverage.Predecessor.Cut.Projection.Samples.Coordinates.Basic
import Pm4Lean.Util.NatListBasis
import Pm4Lean.Util.NatListBasis.Transfer

namespace Pm4Lean
namespace Petri

namespace FiringSequence

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_greedy
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    (samples : List (PrefixCutSample N M₀ ts Mend)) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      (natListGreedyBasis (prefixCutSampleCoordinateLists samples)) := by
  rw [noComparablePrefixCutPredecessorCoordinateListsDominatedBy_iff_dominatedBy]
  intro sample hSampleMem _hNoPredecessor
  exact natListGreedyBasis_dominatesAll
    (prefixCutSampleCoordinateLists samples)
    (Marking.placeValues N sample.marking)
    (mem_prefixCutSampleCoordinateLists_of_mem hSampleMem)

theorem noComparablePrefixCutPredecessorCoordinateListsDominatedBy_of_greedy_dominated
    {N : Net} {M₀ Mend : N.Marking} {ts : List N.Transition}
    {samples : List (PrefixCutSample N M₀ ts Mend)}
    {coordinates : List (List Nat)}
    (hGreedyDominated :
      NatListBasisDominatesAll
        (natListGreedyBasis (prefixCutSampleCoordinateLists samples))
        coordinates) :
    NoComparablePrefixCutPredecessorCoordinateListsDominatedBy samples
      coordinates := by
  rw [noComparablePrefixCutPredecessorCoordinateListsDominatedBy_iff_dominatedBy]
  intro sample hSampleMem _hNoPredecessor
  exact natListBasisDominatesAll_of_greedy_dominated hGreedyDominated
    (Marking.placeValues N sample.marking)
    (mem_prefixCutSampleCoordinateLists_of_mem hSampleMem)

end FiringSequence
end Petri
end Pm4Lean
